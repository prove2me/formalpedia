-- Prove2me | Definitions.Def_OAIQ081S019
-- name    : OAIQ081S019
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:24:46.783409+00:00
-- url     : https://prove2.me/theorems/062a428e-a037-4554-a517-b9b589bcf6c2
-- title:
--   Definitions bundle OAIQ081S019 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 248 declarations of OpenAI's Lean: 149 definitions, 3 inductive types or structures and 96 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.combinedConstant`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.combinedExponent`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.dimensionPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.prepareCopies`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramAnd.jointTrue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramAnd.nextRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramAnd.stackData`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramAnd.steps`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramAnd.weight`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates.callbackCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates.scoreBits`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates.scoreRecords`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates.validPayload`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramPrefix.flag`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramPrefix.loopCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramPrefix.score`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramPrefix.unary`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Emit.unary`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceProgram.inputBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceProgram.runtimeBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingLoaderProgram.captureClears`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingLoaderProgram.captureCopies`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingLoaderProgram.coordinatePorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingLoaderProgram.parameterCopies`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingLoaderProgram.radiusPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingLoaderProgram.unaryRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingPrefixProgram.Ports`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingPrefixProgram.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingPrefixProgram.readStack`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingPrefixProgram.unary`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.environment`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.mergePorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.mergeRegisters`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.metadata`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.prefixABI`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.prefixPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.prefixRegisters`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.weightPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Streams.low`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Zip.firstScores` and 112 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram`, `SubexponentialSAT_SqrtLog_PackingCallerProgramEnvelope`, `SubexponentialSAT_SqrtLog_PackingCallerProgramPrepare`, `SubexponentialSAT_SqrtLog_PackingHeadProgramAnd`, `SubexponentialSAT_SqrtLog_PackingHeadProgramCandidates`, `SubexponentialSAT_SqrtLog_PackingHeadProgramCandidatesBounds`, `SubexponentialSAT_SqrtLog_PackingHeadProgramCandidatesRun`, `SubexponentialSAT_SqrtLog_PackingHeadProgramPrefix`, `SubexponentialSAT_SqrtLog_PackingHeadProgramPreserve`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputEmit`, `SubexponentialSAT_SqrtLog_PackingIncidenceProgram`, `SubexponentialSAT_SqrtLog_PackingLoaderProgramCapture`, `SubexponentialSAT_SqrtLog_PackingLoaderProgramFinish`, `SubexponentialSAT_SqrtLog_PackingLoaderProgramFrame`, `SubexponentialSAT_SqrtLog_PackingLoaderProgramParameters`, `SubexponentialSAT_SqrtLog_PackingPrefixProgram`, `SubexponentialSAT_SqrtLog_PackingPrefixProgramLift`, `SubexponentialSAT_SqrtLog_PackingPrefixProgramRun`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyBasic`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyHeadSetup`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyMerge`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyMetadata`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyWeights`, `SubexponentialSAT_SqrtLog_PackingProgramCombine`, `SubexponentialSAT_SqrtLog_PackingProgramCounts`, `SubexponentialSAT_SqrtLog_PackingProgramEmit`, `SubexponentialSAT_SqrtLog_PackingProgramReducedWeights`, `SubexponentialSAT_SqrtLog_PackingProgramScores`, `SubexponentialSAT_SqrtLog_PackingProgramZip`, `SubexponentialSAT_SqrtLog_PackingWeightProgramBasic`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyBranch`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyCoordinate`, `SubexponentialSAT_SqrtLog_PerturbationEmitProgram`, `SubexponentialSAT_SubexpIncidencePlanProgram`, `SubexponentialSAT_SubexpInputZip`, `SubexponentialSAT_SubexpScopeMembershipProgram`, `SubexponentialSAT_Subexp_ActivePlanProgram`, `SubexponentialSAT_Subexp_AssignmentInitProgram`, `SubexponentialSAT_Subexp_AssignmentInputCall`, `SubexponentialSAT_Subexp_BasisTransposePlanProgram`, `SubexponentialSAT_Subexp_CandidateArrayProgram`, `SubexponentialSAT_Subexp_CandidateScoreProgram`, `SubexponentialSAT_Subexp_CollisionGenerateProgram`, `SubexponentialSAT_Subexp_CollisionStreamProgram`, `SubexponentialSAT_Subexp_CollisionTupleProgram`, `SubexponentialSAT_Subexp_LocalExpectation`, `SubexponentialSAT_Subexp_MinimumProgram`, `SubexponentialSAT_Subexp_OneHotAlphabetProgram`, `SubexponentialSAT_Subexp_PairPlanPreparation`, `SubexponentialSAT_Subexp_PairPreparationBounds`, `SubexponentialSAT_Subexp_PairPreparationProgram`, `SubexponentialSAT_Subexp_PairScoreProgram`, `SubexponentialSAT_Subexp_ReadPlan`, `SubexponentialSAT_Subexp_ScoreBuilderBounds`, `SubexponentialSAT_Subexp_ScoreBuilderPorts`, `SubexponentialSAT_Subexp_SelectionTableProgram`, `SubexponentialSAT_Subexp_SelectorIndices`, `SubexponentialSAT_Subexp_SelectorPairProgram`, `SubexponentialSAT_Subexp_SequentialProgram`, `SubexponentialSAT_Subexp_SequentialStep`, `SubexponentialSAT_Subexp_UnaryCompare`, `SubexponentialSAT_Subexp_UnaryTally`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S040`, `OAIQ081S041` and `OAIQ081S042`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ081_SAT.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete components of the sharp clause/core search from Appendix A.
The guard counts actual framed literals and executes the preserving subset tester.
The complete search and its polynomial resource bound are developed separately below. -/


namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram

def masked {α : Type*} : List Bool → List α → List α
  | _, [] => []
  | mask, x :: xs => if mask.headD false then x :: masked mask.tail xs else masked mask.tail xs

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_LocalExpectation
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

open scoped BigOperators

variable {I W J : Type*} [DecidableEq I]

theorem cast_sum_map (xs : List W) (f : W → ℕ) :
    (((xs.map f).sum : ℕ) : ℚ) = (xs.map (fun w => (f w : ℚ))).sum := by
  induction xs with
  | nil => simp
  | cons w xs ih => simp [ih]

theorem sum_map_div (xs : List W) (f : W → ℚ) (d : ℚ) :
    (xs.map (fun w => f w / d)).sum = (xs.map f).sum / d := by
  induction xs with
  | nil => simp
  | cons w xs ih => simp [ih, add_div]

end SubexponentialSAT.Subexp.LocalExpectation

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

section PartialAssignments

variable {W : Type*}

/-- First-match lookup table for the selector, built by one finite recursion. -/
def selectionTable (currentSize : ℕ) : List ℕ → List (ℕ × ℕ)
  | [] => []
  | n :: remaining => (n, currentSize) :: selectionTable (currentSize + 1) remaining

@[simp] theorem selectionTable_length (currentSize : ℕ) (remaining : List ℕ) :
    (selectionTable currentSize remaining).length = remaining.length := by
  induction remaining generalizing currentSize with
  | nil => rfl
  | cons n remaining ih => simp [selectionTable, ih]

theorem selectionTable_lookup (currentSize : ℕ) (remaining : List ℕ) (n : ℕ) :
    (selectionTable currentSize remaining).lookup n =
      if n ∈ remaining then some (currentSize + remaining.idxOf n) else none := by
  induction remaining generalizing currentSize with
  | nil => simp [selectionTable]
  | cons a remaining ih =>
    by_cases hna : n = a
    · subst n
      simp [selectionTable ]
    · simp [selectionTable, List.lookup_cons, hna, Ne.symm hna, beq_false_of_ne hna, ih, Nat.add_comm, Nat.add_left_comm]

end PartialAssignments

end SubexponentialSAT.Subexp.ReadPlan

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

def gatherRegs : Fin 3 → Fin 5 := Fin.castAdd 2

theorem gatherRegs_injective : Function.Injective gatherRegs := by
  intro a b h
  exact Fin.ext (congrArg (fun j : Fin 5 => j.val) h)

def leftPorts : Fin 10 → Fin 13 := Fin.castAdd 3

def rightPorts (i : Fin 10) : Fin 13 :=
  if i = 1 then 12 else if i = 8 then 10 else leftPorts i

theorem leftPorts_injective : Function.Injective leftPorts := by
  intro a b h
  exact Fin.ext (congrArg (fun j : Fin 13 => j.val) h)

theorem rightPorts_injective : Function.Injective rightPorts := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [rightPorts, leftPorts]

/-- The source bound can be read from the unary plans and word width alone;
the table contents do not affect it. -/
def planBudget (width : ℕ) (left right : List ℕ) : ℕ :=
  34 + (14 * width + 16) * (left.sum + right.sum) +
    (32 * width + 27) * left.length + (23 * width + 27) * right.length

end SubexponentialSAT.Subexp.CollisionStreamProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputEmit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed writer for one double-framed two-address incidence plan. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Emit
open SubexponentialSAT.Subexp

abbrev unary (n : ℕ) := List.replicate n true
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Emit

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CandidateArrayProgram
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

def replacePorts : Fin 8 → Fin 10 := ![8, 1, 9, 3, 4, 5, 6, 7]

theorem replacePorts_injective : Function.Injective replacePorts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [replacePorts]

def sourceCost (originalSize position width : ℕ) : ℕ :=
  7 * originalSize + 7 * position + position * (14 * width + 10) + 20 * width + 32

end SubexponentialSAT.Subexp.CandidateArrayProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CollisionTupleProgram
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

structure Frame where
  current : List Bool
  width : List Bool
  left : List ℕ
  right : List ℕ
  tail : List Bool

def lowRegs : Fin 5 → Fin 8 := Fin.castAdd 3
def lowStacks : Fin 13 → Fin 18 := Fin.castAdd 5

theorem lowRegs_injective : Function.Injective lowRegs := by
  intro i j h; exact Fin.ext (congrArg (fun k : Fin 8 => k.val) h)

theorem lowStacks_injective : Function.Injective lowStacks := by
  intro i j h; exact Fin.ext (congrArg (fun k : Fin 18 => k.val) h)

/-- This schema only describes the serialized tuple's row widths and the
validity of the two numeric plans. It places no condition on the answer bit. -/
def validPayload (current : List (List Bool)) (width : ℕ) (left right : List ℕ)
    (bits : List Bool) : Prop :=
  ∃ candidate : List (List Bool), candidate.flatten = bits ∧
    (∀ row ∈ current ++ candidate, row.length = width) ∧
    (∀ i ∈ left, i < (current ++ candidate).length) ∧
    (∀ i ∈ right, i < (current ++ candidate).length)

end SubexponentialSAT.Subexp.CollisionTupleProgram

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

def pairStacks (xs ys : List Bool) : Fin 2 → List Bool :=
  fun i => if i = 0 then xs else ys

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

def pairStacks (xs out : List Bool) : Fin 2 → List Bool :=
  fun i => if i = 0 then xs else out

def loopRegs : Fin 2 → Bool := fun i => decide (i = 1)

def steps : List Bool → ℕ
  | [] => 3
  | b :: xs => (if b then 5 else 3) + steps xs

theorem replicate_append_bit (n : ℕ) (out : List Bool) :
    List.replicate n false ++ false :: out = List.replicate (n + 1) false ++ out := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ, List.cons_append] using congrArg (List.cons false) ih

end SubexponentialSAT.Subexp.UnaryTally

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

def resetValues (indices : List (Fin 10)) (regs : Fin 10 → Bool) : Fin 10 → Bool :=
  indices.foldl (fun rs i => Function.update rs i false) regs

theorem resetValues_apply (indices : List (Fin 10)) (regs : Fin 10 → Bool) (i : Fin 10) :
    resetValues indices regs i = if i ∈ indices then false else regs i := by
  induction indices generalizing regs with
  | nil => simp [resetValues]
  | cons j rest ih =>
    change resetValues rest (Function.update regs j false) i = _
    rw [ih]
    by_cases hi : i = j <;> by_cases hr : i ∈ rest <;>
      simp_all []

def streamRegs : Fin 8 → Fin 10 := Fin.castAdd 2
def streamPorts : Fin 18 → Fin 20 := Fin.castAdd 2

theorem streamRegs_injective : Function.Injective streamRegs := by
  intro i j h; exact Fin.ext (congrArg (fun k : Fin 10 => k.val) h)

theorem streamPorts_injective : Function.Injective streamPorts := by
  intro i j h; exact Fin.ext (congrArg (fun k : Fin 20 => k.val) h)

def TupleSchema (alphabet : List (List Bool)) (count : ℕ) (bits : List Bool) : Prop :=
  ∃ rows : List (List Bool), rows.length = count ∧ rows.flatten = bits ∧
    ∀ row ∈ rows, row ∈ alphabet

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

def resetValues (indices : List (Fin 13)) (regs : Fin 13 → Bool) : Fin 13 → Bool :=
  indices.foldl (fun rs i => Function.update rs i false) regs

def generatorRegs : Fin 10 → Fin 13 := Fin.castAdd 3
def generatorPorts : Fin 20 → Fin 26 := Fin.castAdd 6

theorem generatorRegs_injective : Function.Injective generatorRegs := by
  intro i j h; exact Fin.ext (congrArg (fun k : Fin 13 => k.val) h)

theorem generatorPorts_injective : Function.Injective generatorPorts := by
  intro i j h; exact Fin.ext (congrArg (fun k : Fin 26 => k.val) h)

theorem any_false (records : List (List Bool)) :
    records.any (fun _ => false) = false := by
  induction records <;> simp_all

def tallyRegs : Fin 2 → Fin 13 := Fin.castAdd 11
def tallyPorts : Fin 2 → Fin 26 := fun i => if i = 0 then 11 else 18

theorem tallyRegs_injective : Function.Injective tallyRegs := by
  intro i j h; exact Fin.ext (congrArg (fun k : Fin 13 => k.val) h)

theorem tallyPorts_injective : Function.Injective tallyPorts := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [tallyPorts]

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

def arrayRegisters : Fin 2 → Fin 16 := ![0,1]
def arrayStacks : Fin 10 → Fin 36 := ![26,27,28,3,0,1,2,4,13,5]

theorem arrayRegisters_injective : Function.Injective arrayRegisters := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [arrayRegisters]
theorem arrayStacks_injective : Function.Injective arrayStacks := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [arrayStacks]

def pairStartRegs : Fin 16 → Bool := fun i => decide (i = 14)
def scoredRegs : Fin 16 → Bool := fun i => decide (i = 11 ∨ i = 14)
def finishedRegs : Fin 16 → Bool := fun i => decide (i = 2 ∨ i = 11 ∨ i = 14)

end SubexponentialSAT.Subexp.CandidateScoreProgram

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

abbrev Regs := Fin 10 → Bool

def low7 : Fin 7 → Fin 10 := Fin.castAdd 3
def low5 : Fin 5 → Fin 12 := Fin.castAdd 7

theorem low7_injective : Function.Injective low7 := Fin.castAdd_injective 7 3
theorem low5_injective : Function.Injective low5 := Fin.castAdd_injective 5 7

def low4 : Fin 4 → Fin 10 := Fin.castAdd 6
def compareStack : Fin 2 → Fin 12 := ![9, 10]
theorem low4_injective : Function.Injective low4 := Fin.castAdd_injective 4 6
theorem compareStack_injective : Function.Injective compareStack := by decide

def emitRegs : Fin 3 → Fin 10 := ![0, 1, 9]
def emitStack : Fin 4 → Fin 12 := ![5, 7, 8, 2]
theorem emitRegs_injective : Function.Injective emitRegs := by decide
theorem emitStack_injective : Function.Injective emitStack := by decide

abbrev flags (regs : Regs) (v p f : Bool) : Regs :=
  Function.update (Function.update (Function.update regs 0 v) 1 p) 9 f

@[simp] theorem flags_self (regs : Regs) : flags regs (regs 0) (regs 1) (regs 9) = regs := by
  funext i
  fin_cases i <;> simp [flags]

def keep (records : List (List Bool)) (threshold : List Bool) (bits : List Bool) : Bool :=
  decide (threshold.length ≤ bits.length ∧ bits ∈ records)

abbrev outerFlags (regs : Regs) (v p f : Bool) : Regs :=
  Function.update (Function.update (Function.update regs 7 v) 8 p) 9 f

@[simp] theorem outerFlags_self (regs : Regs) :
    outerFlags regs (regs 7) (regs 8) (regs 9) = regs := by
  funext i
  fin_cases i <;> simp [outerFlags]

def reverseStack : Fin 4 → Fin 12 := ![8, 7, 11, 2]
theorem reverseStack_injective : Function.Injective reverseStack := by decide

def unary (n : ℕ) : List Bool := List.replicate n true

def indexRecords (positions : List ℕ) : List (List Bool) := positions.map unary

end SubexponentialSAT.Subexp.ActivePlanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PairPlanPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual parsing and record-order preparation of the two plans in a pair
payload. Registers 0, 1, and 2 are scratch; all other registers are framed. -/

namespace SubexponentialSAT.Subexp.PairPlanPreparation

def smallRegs : Fin 3 → Fin 16 := Fin.castAdd 13
def reversePorts (src dst : Fin 34) : Fin 4 → Fin 34 := ![src, 1, dst, 4]

theorem smallRegs_injective : Function.Injective smallRegs := by
  intro i j h; exact Fin.ext (congrArg (fun k : Fin 16 => k.val) h)

end SubexponentialSAT.Subexp.PairPlanPreparation

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

def unaryIndex (n : ℕ) : List Bool := List.replicate n true

@[simp] theorem unaryIndex_length (n : ℕ) : (unaryIndex n).length = n := by
  simp [unaryIndex]

@[simp] theorem unaryIndex_reverse (n : ℕ) : (unaryIndex n).reverse = unaryIndex n := by
  simp [unaryIndex]

theorem unaryIndex_injective : Function.Injective unaryIndex := by
  intro m n h
  simpa using congrArg List.length h

def encodeEntries (entries : List (ℕ × ℕ)) : List (List Bool × List Bool) :=
  entries.map (fun p => (unaryIndex p.1, unaryIndex p.2))

theorem encodeEntries_lookup (entries : List (ℕ × ℕ)) (n : ℕ) :
    (encodeEntries entries).lookup (unaryIndex n) =
      (entries.lookup n).map unaryIndex := by
  induction entries with
  | nil => rfl
  | cons p entries ih =>
      rcases p with ⟨key, value⟩
      by_cases h : n = key
      · subst key
        simp [encodeEntries ]
      · have hu : unaryIndex n ≠ unaryIndex key := fun he => h (unaryIndex_injective he)
        simpa [encodeEntries, List.lookup_cons, beq_false_of_ne h, beq_false_of_ne hu] using ih

def selectionEntries (currentSize : ℕ) (remaining : List ℕ) :
    List (List Bool × List Bool) :=
  encodeEntries (ReadPlan.selectionTable currentSize remaining)

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

def emitStack : Fin 4 → Fin 6 := ![0, 2, 3, 1]

theorem emitStack_injective : Function.Injective emitStack := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [emitStack]

def callbackCost (M n : ℕ) : ℕ := 11 * n + 18 * M + 37

def loopCost (M : ℕ) : List ℕ → ℕ
  | [] => 1
  | n :: remaining =>
      (6 * n + 4) + (callbackCost M n + 2) + loopCost (M + 1) remaining + 1

end SubexponentialSAT.Subexp.SelectionTableProgram

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

def stackMap : Fin 9 → Fin 12 := Fin.castAdd 3

theorem stackMap_injective : Function.Injective stackMap := by
  intro a b h
  exact Fin.ext (congrArg (fun x : Fin 12 => x.val) h)

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

def activeRegs : Fin 10 → Fin 16 := Fin.castAdd 6
def activeStacks : Fin 12 → Fin 34 := Fin.castAdd 22
def tableRegs : Fin 3 → Fin 16 := Fin.castAdd 13
def tableStacks : Fin 6 → Fin 34 := Fin.castAdd 28
def selectorRegs : Fin 8 → Fin 16 := Fin.castAdd 8

/-- Stack 7 holds the cutoff throughout the pair loop and is excluded. -/
def selectorStacks : Fin 12 → Fin 34 := ![0, 1, 2, 4, 5, 11, 6, 3, 8, 9, 10, 29]

def reverseStacks : Fin 4 → Fin 34 := ![29, 1, 28, 4]

theorem activeRegs_injective : Function.Injective activeRegs := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 16 => x.val) h)

theorem activeStacks_injective : Function.Injective activeStacks := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 34 => x.val) h)

theorem tableRegs_injective : Function.Injective tableRegs := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 16 => x.val) h)

theorem tableStacks_injective : Function.Injective tableStacks := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 34 => x.val) h)

theorem selectorRegs_injective : Function.Injective selectorRegs := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 16 => x.val) h)

theorem selectorStacks_injective : Function.Injective selectorStacks := by decide

def resetValues (indices : List (Fin 16)) (regs : Fin 16 → Bool) : Fin 16 → Bool :=
  indices.foldl (fun rs i => Function.update rs i false) regs

def prefixRegs {n : ℕ} (small : Fin n → Bool) (old : Fin 16 → Bool) : Fin 16 → Bool :=
  fun j => if hj : j.val < n then small ⟨j.val, hj⟩ else old j

end SubexponentialSAT.Subexp.PairPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PairPreparationBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Uniform polynomial bounds for the actual once-per-step pair preparation
program. The common parameter bounds physical input lengths and record count. -/

namespace SubexponentialSAT.Subexp.PairPreparationBounds

open PairPreparationProgram

theorem sum_le_length_mul (xs : List ℕ) (B : ℕ) (h : ∀ n ∈ xs, n ≤ B) :
    xs.sum ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons n ns ih =>
    have hn := h n (by simp)
    have ht := ih (fun m hm => h m (by simp [hm]))
    simp only [List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem member_le_sum {n : ℕ} {xs : List ℕ} (h : n ∈ xs) : n ≤ xs.sum := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · have := ih h; simp only [List.sum_cons]; omega

end SubexponentialSAT.Subexp.PairPreparationBounds

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

def compareRegs : Fin 4 → Fin 9 := Fin.natAdd 5
def compareStacks (i : Fin 2) : Fin 8 := if i = 0 then 3 else 4

theorem compareRegs_injective : Function.Injective compareRegs := by
  intro i j h
  exact (Fin.natAdd_inj 5).mp h

theorem compareStacks_injective : Function.Injective compareStacks := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [compareStacks]

def pick (a b : ℕ × ℕ) : ℕ × ℕ := if a.1 ≤ b.1 then a else b

def scan (current : ℕ × ℕ) (next : ℕ) : List (List Bool) → ℕ × ℕ
  | [] => current
  | bits :: rest => scan (pick current (bits.length, next)) (next + 1) rest

def tagged (next : ℕ) : List (List Bool) → List (ℕ × ℕ)
  | [] => []
  | bits :: rest => (bits.length, next) :: tagged (next + 1) rest

theorem pick_assoc (a b c : ℕ × ℕ) : pick (pick a b) c = pick a (pick b c) := by
  by_cases hab : a.1 ≤ b.1 <;> by_cases hbc : b.1 ≤ c.1 <;>
    by_cases hac : a.1 ≤ c.1 <;> simp [pick, hab, hbc, hac] <;> omega

/-- A sum of actual per-record bounds, with the unary index increasing. -/
def scanBudget (M j : ℕ) : List (List Bool) → ℕ
  | [] => 1
  | bits :: rest => 107 * (M + bits.length + j + 1) + scanBudget M (j + 1) rest

theorem scanBudget_le (M j : ℕ) (records : List (List Bool)) :
    scanBudget M j records ≤ 107 *
      ((records.map List.length).sum + records.length * (M + j + records.length + 1)) + 1 := by
  induction records generalizing j with
  | nil => simp [scanBudget]
  | cons bits rest ih =>
      have h := ih (j + 1)
      simp only [scanBudget, List.map_cons, List.sum_cons, List.length_cons]
      nlinarith

/-- The score/index pair selected by the first-minimum rule. -/
def firstMinimum (first : List Bool) (rest : List (List Bool)) : ℕ × ℕ :=
  scan (first.length, 0) 1 rest

theorem sourceBudget_le_quadratic (first : List Bool) (rest : List (List Bool)) :
    15 * first.length + 19 + scanBudget first.length 1 rest ≤
      500 * (first.length + (rest.map List.length).sum + rest.length + 1) ^ 2 := by
  have h := scanBudget_le first.length 1 rest
  have hsq := Nat.mul_self_le_mul_self
    (show rest.length ≤ first.length + (rest.map List.length).sum + rest.length + 1 by omega)
  nlinarith [Nat.zero_le ((rest.map List.length).sum * first.length),
    Nat.zero_le ((rest.map List.length).sum * rest.length),
    Nat.zero_le (first.length * first.length)]

/-- An indexed specification of the same earliest-minimum rule. -/
def indexChoice {A : Type*} (score : A → ℕ) (next : ℕ) (a : A) : List A → ℕ × A
  | [] => (next, a)
  | b :: bs =>
      let c := indexChoice score (next + 1) b bs
      if score a ≤ score c.2 then (next, a) else c

theorem indexChoice_lookup {A : Type*} (score : A → ℕ)
    (next : ℕ) (a : A) (tail : List A) :
    ∃ k < (a :: tail).length, (indexChoice score next a tail).1 = next + k ∧
      (a :: tail)[k]? = some (indexChoice score next a tail).2 := by
  induction tail generalizing next a with
  | nil => exact ⟨0, by simp, by simp [indexChoice], rfl⟩
  | cons b bs ih =>
      obtain ⟨k, hk, hi, hv⟩ := ih (next + 1) b
      by_cases h : score a ≤ score (indexChoice score (next + 1) b bs).2
      · exact ⟨0, by simp, by simp [indexChoice, h], by simp [indexChoice, h]⟩
      · refine ⟨k + 1, by simpa using Nat.succ_lt_succ hk, ?_, ?_⟩
        · simpa [indexChoice, h, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hi
        · simpa [indexChoice, h] using hv

end SubexponentialSAT.Subexp.MinimumProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SequentialProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed sequential assignment control

The loop counter, processed index, word width, alphabet, and assignment are
runtime stack data. A fixed score-building command is composed with the
verified minimum selector and preserving packed-array operations.
-/

namespace SubexponentialSAT.Subexp.SequentialProgram

def minimumRegisters : Fin 9 → Fin 16 := Fin.castAdd 7
def minimumStacks : Fin 8 → Fin 48 := Fin.castAdd 40

theorem minimumRegisters_injective : Function.Injective minimumRegisters := by
  intro a b h
  have hv := congrArg (fun x : Fin 16 => x.val) h
  exact Fin.ext hv

theorem minimumStacks_injective : Function.Injective minimumStacks := by
  intro a b h
  have hv := congrArg (fun x : Fin 48 => x.val) h
  exact Fin.ext hv

abbrev readPorts : Fin 8 → Fin 48 := ![9, 12, 7, 10, 13, 14, 15, 16]
abbrev replacePorts : Fin 8 → Fin 48 := ![8, 12, 17, 10, 13, 14, 15, 16]

abbrev readEmbedding : Fin 8 ↪ Fin 48 := ⟨readPorts, by decide⟩
abbrev replaceEmbedding : Fin 8 ↪ Fin 48 := ⟨replacePorts, by decide⟩

def scratchPorts : Finset (Fin 48) := {0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 14, 15, 16, 17, 18}

/-- All mathematical values in this invariant describe concrete packed
arrays or lengths of concrete unary stacks. -/
structure Memory {A : Type*} (encode : A → List Bool) (a : A) (tail : List A)
    (remaining : ℕ) (fixed : List A) (stk : Fin 48 → List Bool) : Prop where
  assignment : stk 8 = (fixed.reverse.map encode ++ List.replicate remaining (encode a)).flatten
  alphabet : stk 9 = ((a :: tail).map encode).flatten
  width : (stk 10).length = (encode a).length
  processed : (stk 19).length = fixed.length
  scratch : ∀ j ∈ scratchPorts, stk j = []

/-- Runtime read-only tables and restored scratch outside the controller ABI. -/
def HighState (environment stk : Fin 48 → List Bool) : Prop :=
  ∀ j, 20 ≤ j.val → stk j = environment j

theorem highState_counter_update {environment stk : Fin 48 → List Bool}
    (h : HighState environment stk) (counter : List Bool) :
    HighState environment (Function.update stk 11 counter) := by
  intro j hj
  have hne : j ≠ 11 := by intro heq; subst j; omega
  simpa [hne] using h j hj

theorem memory_counter_update {A : Type*} {encode : A → List Bool} {a : A}
    {tail : List A} {n : ℕ} {fixed : List A} {stk : Fin 48 → List Bool}
    (h : Memory encode a tail n fixed stk) (counter : List Bool) :
    Memory encode a tail n fixed (Function.update stk 11 counter) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa using h.assignment
  · simpa using h.alphabet
  · simpa using h.width
  · simpa using h.processed
  · intro j hj
    have hj11 : j ≠ 11 := by
      intro heq
      subst j
      exact (show (11 : Fin 48) ∉ scratchPorts by decide) hj
    simpa [hj11] using h.scratch j hj

end SubexponentialSAT.Subexp.SequentialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_ScoreBuilderPorts
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

def candidatePorts : Fin 36 → Fin 48 :=
  ![0,1,2,10,3,4,5,6,7,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,
    35,36,8,37,19,38,39,40,41,42,43,44]

def preparationPorts : Fin 34 → Fin 48 :=
  ![0,1,2,3,4,5,6,7,20,21,22,23,24,25,26,27,28,29,31,32,33,35,36,37,
    38,41,42,43,44,40,46,45,47,19]

theorem candidatePorts_injective : Function.Injective candidatePorts := by decide
theorem preparationPorts_injective : Function.Injective preparationPorts := by decide

/-- Runtime tables are data on six fixed stack ports. All other high ports are
empty at a complete scorer-call boundary. -/
def environment (alphabet depth rawPairs seedIndices seedCount : List Bool) : Fin 48 → List Bool :=
  fun j => if j = 30 then alphabet else if j = 34 then depth
    else if j = 39 then alphabet else if j = 45 then rawPairs
    else if j = 46 then seedIndices else if j = 47 then seedCount else []

end SubexponentialSAT.Subexp.ScoreBuilderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_ScoreBuilderBounds
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

open ScoreBuilderProgram

def runtimeBound (B q depth : ℕ) : ℕ := 10000 * 31 ^ 6 * (B + 1) ^ 12 * q ^ depth

end SubexponentialSAT.Subexp.ScoreBuilderBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SequentialStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete composition of score selection and packed assignment update. -/

namespace SubexponentialSAT.Subexp.SequentialProgram

theorem lookup_split {A : Type*} (xs : List A) (k : ℕ) (x : A)
    (h : xs[k]? = some x) :
    ∃ before after, xs = before ++ x :: after ∧ before.length = k := by
  induction xs generalizing k with
  | nil => simp at h
  | cons a xs ih =>
      cases k with
      | zero =>
          have ha : a = x := by simpa using h
          subst a
          exact ⟨[], xs, rfl, rfl⟩
      | succ k =>
          obtain ⟨before, after, hs, hl⟩ := ih k (by simpa using h)
          exact ⟨a :: before, after, by simp [hs], by simp [hl]⟩

theorem sum_scores_le {A : Type*} (xs : List A) (score : A → ℕ) (S : ℕ)
    (h : ∀ x ∈ xs, score x ≤ S) : (xs.map score).sum ≤ xs.length * S := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have ha := h a (by simp)
      have ht := ih (fun x hx => h x (by simp [hx]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith

def cleanPorts : List (Fin 48) := [0, 1, 2, 3, 4, 5, 6, 7, 12]

theorem scratch_partition (j : Fin 48) (hj : j ∈ scratchPorts) :
    j ∈ cleanPorts ∨ 13 ≤ j.val ∧ j.val ≤ 18 := by
  exact (show ∀ j : Fin 48, j ∈ scratchPorts →
    j ∈ cleanPorts ∨ 13 ≤ j.val ∧ j.val ≤ 18 by decide) j hj

end SubexponentialSAT.Subexp.SequentialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete incidence collision scoring from raw two-word read plans.
The fixed legacy program constructs its selection tables and all four-word
completion tuples at runtime. No precomputed collision table is an input. -/

namespace SubexponentialSAT.SqrtLog.PackingIncidenceProgram

open SubexponentialSAT.Subexp

/-- Fixed polynomial in the original input sizes, before preparing any table. -/
def inputBound (M pairs q width : ℕ) : ℕ := 32 * (M + pairs + q + width + 1)^2

def runtimeBound (M pairs q width : ℕ) : ℕ :=
  ScoreBuilderBounds.runtimeBound (inputBound M pairs q width) q 4

end SubexponentialSAT.SqrtLog.PackingIncidenceProgram

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

theorem cost_bound {q L x n : ℕ}
    (hn : n ≤ (20 * q + 30) * L + 3) (hx : x ≤ L) :
    (3 * L + 3) + (n + ((2 * x + 3) + 5)) ≤ 128 * (q + 1) * (L + 1) := by
  nlinarith

end SubexponentialSAT.SubexpScopeMembershipProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIncidencePlanProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Encoded scopes to a concrete incidence read plan

This is one fixed finite program. Runtime stacks supply the encoded scope list,
the vertex token, and unary D and Delta. No slot assignment is supplied to the
machine. Incident slots are allocated in outer-list encounter order.
-/
namespace SubexponentialSAT.SubexpIncidencePlanProgram

abbrev unary (n : ℕ) := List.replicate n true

end SubexponentialSAT.SubexpIncidencePlanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramScores
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Denominator-cleared scores for incidence/head conditional expectation. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram
open SubexponentialSAT.Subexp.LocalExpectation

section General
variable {A W J : Type*} [DecidableEq A]

theorem sum_map_le_bound (xs : List J) (f : J → ℕ) (B : ℕ)
    (hf : ∀ j, f j ≤ B) : (xs.map f).sum ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons j xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    calc
      _ ≤ B + xs.length * B := Nat.add_le_add (hf j) ih
      _ = _ := by ring

end General

end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Splitting all weighted completions into two unweighted integer counts. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram
open SubexponentialSAT.Subexp.LocalExpectation

theorem sum_linear {J : Type*} (xs : List J) (f g : J → ℕ) (a b : ℕ) :
    (xs.map (fun j => a*f j+b*g j)).sum = a*(xs.map f).sum+b*(xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons j xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingLoaderProgramFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Framing and paid parameter serialization for the packing loader. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram


def unaryRegs : Fin 3 ↪ Fin 16 := ⟨Fin.castAdd 13,Fin.castAdd_injective _ _⟩

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingLoaderProgramCapture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Consume the incidence installer's transient metadata while preserving an
explicit raw-scope master outside the selector's48-stack bank. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

def captureCopies : List (Fin 64 × Fin 64) := [(32,60),(33,4),(35,5)]
def captureClears : List (Fin 64) := [32,33,34,35]

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentInitProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical initialization of the sequential assignment memory

The input contains the already generated alphabet and incidence records.
This fixed routine duplicates the runtime tables, creates the initial packed
assignment by actual repeated copying, and clears all temporary ports. The
production of the input records is a separate frontend stage.
-/

namespace SubexponentialSAT.Subexp.AssignmentInitProgram

def copyRegisters : Fin 3 → Fin 16 := Fin.castAdd 13
def copyPorts : Fin 4 → Fin 48 := ![0, 8, 1, 2]

theorem copyRegisters_injective : Function.Injective copyRegisters := by
  intro i j h
  exact Fin.ext (congrArg (fun z : Fin 16 => z.val) h)

theorem copyPorts_injective : Function.Injective copyPorts := by decide

end SubexponentialSAT.Subexp.AssignmentInitProgram

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

abbrev unary (n : ℕ) := List.replicate n true

def repeatRegisters : Fin 3 → Fin 5 := Fin.castAdd 2
def repeatStacks : Fin 4 → Fin 7 := ![5, 2, 4, 3]

theorem repeatRegisters_injective : Function.Injective repeatRegisters := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 5 => x.val) h)

theorem repeatStacks_injective : Function.Injective repeatStacks := by decide

def resetThree (regs : Fin 5 → Bool) : Fin 5 → Bool :=
  fun j => if j.val < 3 then false else regs j

def bodyCost (i n : ℕ) : ℕ := 12 * i + 26 * n + 30

end SubexponentialSAT.Subexp.OneHotAlphabetProgram

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

def work : List (Fin 48) := List.ofFn (fun i : Fin 10 => ⟨12 + i.val, by omega⟩)

theorem mem_work (j : Fin 48) : j ∈ work ↔ 12 ≤ j.val ∧ j.val < 22 := by
  simp only [work, List.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩
    change 12 ≤ 12 + i.val ∧ 12 + i.val < 22
    have := i.isLt
    omega
  · rintro ⟨hlo, hhi⟩
    exact ⟨⟨j.val - 12, by omega⟩, Fin.ext (by simp; omega)⟩

def stack {s : ℕ} (hs : s ≤ 10) (i : Fin s) : Fin 48 := ⟨12 + i.val, by omega⟩
def register {r : ℕ} (hr : r ≤ 16) (i : Fin r) : Fin 16 := i.castLE hr

theorem stack_injective {s : ℕ} (hs : s ≤ 10) : Function.Injective (stack hs) := by
  intro i j h
  apply Fin.ext
  have h' := congrArg Fin.val h
  simpa [stack] using h'

theorem register_injective {r : ℕ} (hr : r ≤ 16) : Function.Injective (register hr) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin 16 => x.val) h

theorem stack_mem {s : ℕ} (hs : s ≤ 10) (i : Fin s) : stack hs i ∈ work := by
  rw [mem_work]
  have := i.isLt
  simp only [stack, Fin.val_mk]
  omega

end SubexponentialSAT.Subexp.AssignmentInputCall

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingLoaderProgramFinish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Install the packing scorer's depth and binary parameter bank after the
native alphabet/assignment producer has finished using its low workspace. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
open SubexponentialSAT.Subexp
attribute [local simp] Fin.coe_ofNat_eq_mod

def parameterCopies : List (Fin 64 × Fin 64) := [(56,20),(57,21),(58,22),(59,23)]

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingLoaderProgramParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid conversion of the actual binary radius and coordinate parameters. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

def radiusPorts : Fin 14 ↪ Fin 64 :=
  ⟨![59,1,3,4,5,6,7,8,9,10,11,12,13,14],by decide⟩
def coordinatePorts : Fin 14 ↪ Fin 64 :=
  ⟨![55,2,3,4,5,6,7,8,9,10,11,12,13,14],by decide⟩

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete stack transport for the combined packing score producer. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly

/-- Runtime metadata occupies high20..23 at boundaries and spare12..15
while the incidence subroutine uses its own high work bank. -/
def metadata : List (Fin 48 × Fin 48) := [(20,12),(21,13),(22,14),(23,15)]

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyMetadata
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid parking of four runtime integer parameters around the incidence scorer. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.Subexp

def environment (old : Fin 48 → List Bool) (n s M r : List Bool) : Fin 48 → List Bool :=
  fun j => if j=20 then n else if j=21 then s else if j=22 then M else if j=23 then r else old j

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

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
open SubexponentialSAT

def jointTrue (xs ys : List Bool) : ℕ := (List.zipWith (· && ·) xs ys).count true

def stackData (xs ys out : List Bool) : Fin 3 → List Bool := ![xs,ys,out]

def nextRegs (regs : Fin 5 → Bool) (a b : Bool) : Fin 5 → Bool :=
  ![a,true,b,true,if a && b then false else regs 4]

def weight (a b : Bool) : ℕ := if a then (if b then 7 else 5) else 4

def steps : List Bool → List Bool → ℕ
  | a::xs,b::ys => weight a b+steps xs ys
  | _,_ => 6

theorem steps_le (xs ys : List Bool) (hlen : xs.length=ys.length) :
    steps xs ys ≤ 7*xs.length+6 := by
  induction xs generalizing ys with
  | nil => simp [steps]
  | cons a xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons b ys =>
      have h := ih ys (by simpa using hlen)
      have hw : weight a b ≤ 7 := by cases a <;> cases b <;> decide
      simp only [steps,List.length_cons]
      omega

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
open SubexponentialSAT

abbrev unary (n : ℕ) := List.replicate n true

def flag (n : ℕ) : Bool := decide (0 < n)

def score (candidate : List Bool) (rows : List (List Bool)) : ℕ :=
  (rows.map (PackingHeadProgramAnd.jointTrue candidate)).sum

def loopCost (candidate : List Bool) : List (List Bool) → ℕ
  | [] => 1
  | word::rows => (7*candidate.length+7+PackingHeadProgramAnd.steps candidate word)+loopCost candidate rows

theorem loopCost_le (candidate : List Bool) (rows : List (List Bool))
    (hlen : ∀ row ∈ rows,row.length=candidate.length) :
    loopCost candidate rows ≤ rows.length*(14*candidate.length+13)+1 := by
  induction rows with
  | nil => simp [loopCost]
  | cons word rows ih =>
    have hs := PackingHeadProgramAnd.steps_le candidate word (hlen word (by simp)).symm
    have ht := ih (by intro row hr; exact hlen row (by simp [hr]))
    simp only [loopCost,List.length_cons]
    nlinarith

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
open SubexponentialSAT
open scoped BigOperators

theorem flatten_length (candidate : List Bool) (rows : List (List Bool))
    (hlen : ∀ row ∈ rows,row.length=candidate.length) :
    rows.flatten.length=rows.length*candidate.length := by
  induction rows with
  | nil => simp
  | cons word rows ih =>
    simp only [List.flatten_cons,List.length_append,List.length_cons]
    rw [hlen word (by simp),ih (by intro row hr; exact hlen row (by simp [hr]))]
    ring

end SubexponentialSAT.SqrtLog.PackingHeadProgramPreserve

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
open SubexponentialSAT.Subexp

def low (i : Fin 8) : Fin 12 := i.castAdd 4
theorem low_injective : Function.Injective low := Fin.castAdd_injective _ _

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
open SubexponentialSAT
open Subexp

def callbackCost (rows : List (List Bool)) (candidate : List Bool) : ℕ :=
  rows.length*(21*candidate.length+20)+11*candidate.length+
    4*PackingHeadProgramPrefix.score candidate rows+41

end SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingHeadProgramCandidatesRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates
open SubexponentialSAT Subexp

def scoreBits (rows : List (List Bool)) (candidate : List Bool) : List Bool :=
  List.replicate (PackingHeadProgramPrefix.score candidate rows) false

def validPayload (rows : List (List Bool)) (bits : List Bool) : Prop :=
  ∀ row ∈ rows,row.length=bits.length

theorem any_false (records : List (List Bool)) : records.any (fun _ => false) = false := by
  induction records <;> simp_all

def scoreRecords (rows candidates : List (List Bool)) : List (List Bool) :=
  candidates.map (scoreBits rows)

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
open SubexponentialSAT Subexp
open scoped BigOperators

theorem jointTrue_le (xs ys : List Bool) : PackingHeadProgramAnd.jointTrue xs ys ≤ xs.length := by
  have h := @List.count_le_length Bool _ true (List.zipWith (· && ·) xs ys)
  exact h.trans (by simp)

theorem score_le (candidate : List Bool) (rows : List (List Bool)) :
    PackingHeadProgramPrefix.score candidate rows ≤ rows.length*candidate.length := by
  induction rows with
  | nil => simp [PackingHeadProgramPrefix.score]
  | cons word rows ih =>
    have h := jointTrue_le candidate word
    simp only [PackingHeadProgramPrefix.score,List.map_cons,List.sum_cons,List.length_cons] at *
    nlinarith

end SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramReducedWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact cancellation of the common q^4 factor in incremental head scores.
This removes q from the two runtime weights when epsilon is 1/s. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram

 def reducedScore (n s M r ci overlap : ℕ) : ℕ :=
  (n*s)^2*ci + 8*(M*r)^2*overlap

 theorem reducedScore_weights (n s M r ci overlap : ℕ) :
    reducedScore n s M r ci overlap = (n^2*s^2)*ci + (8*M^2*r^2)*overlap := by
  unfold reducedScore
  ring

 theorem reducedScore_bound (n s M r ci overlap C H : ℕ) (hc : ci ≤ C) (hh : overlap ≤ H) :
    reducedScore n s M r ci overlap ≤ (n*s)^2*C + 8*(M*r)^2*H := by
  exact Nat.add_le_add (Nat.mul_le_mul_left _ hc) (Nat.mul_le_mul_left _ hh)

 theorem reducedScore_scaled (n s M r q ci overlap : ℕ) :
    (n^2*(s*q^2)^2)*ci + (2*q^4*(M^2*(2*r)^2))*overlap =
      q^4*reducedScore n s M r ci overlap := by
  unfold reducedScore
  ring

 theorem reducedScore_scaled_order (n s M r q ci cj hi hj : ℕ) (hq : 0 < q) :
    (n^2*(s*q^2)^2)*ci + (2*q^4*(M^2*(2*r)^2))*hi ≤
      (n^2*(s*q^2)^2)*cj + (2*q^4*(M^2*(2*r)^2))*hj ↔
    reducedScore n s M r ci hi ≤ reducedScore n s M r cj hj := by
  rw [reducedScore_scaled,reducedScore_scaled]
  constructor
  · intro h
    exact Nat.le_of_mul_le_mul_left h (pow_pos hq 4)
  · exact Nat.mul_le_mul_left _

end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramCombine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed two-call score combiner. Inputs are binary weights and canonical
false-unary collision counts. The only modified port is the score accumulator. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram

def incidenceScaleStacks : Fin 6 → Fin 8 := ![0,1,4,5,6,7]
def headScaleStacks : Fin 6 → Fin 8 := ![2,3,4,5,6,7]

theorem incidenceScaleStacks_injective : Function.Injective incidenceScaleStacks := by decide
theorem headScaleStacks_injective : Function.Injective headScaleStacks := by decide

end SubexponentialSAT.SqrtLog.PackingProgram

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

def regPorts (i : Fin 3) : Fin 8 := i.castAdd 5
def writerPorts : Fin 4 → Fin 8 := ![0, 1, 4, 7]

theorem regPorts_injective : Function.Injective regPorts := Fin.castAdd_injective _ _
theorem writerPorts_injective : Function.Injective writerPorts := by decide

def finishedRegs (regs : Fin 8 → Bool) : Fin 8 → Bool :=
  Function.update (Function.update regs 0 true) 1 false

def rowWords (pairs : List (List Bool × List Bool)) : List (List Bool) := pairs.map Prod.fst
def inputWords (pairs : List (List Bool × List Bool)) : List (List Bool) := pairs.map Prod.snd

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

def zipPorts (i : Fin 8) : Fin 14 := i.castAdd 6
def scorePorts : Fin 12 → Fin 14 := ![12,0,13,1,2,3,4,5,6,7,8,9]

theorem zipPorts_injective : Function.Injective zipPorts := Fin.castAdd_injective _ _
theorem scorePorts_injective : Function.Injective scorePorts := by decide

def rawPairs (ps : List (ℕ × ℕ)) : List (List Bool × List Bool) :=
  ps.map (fun p => (List.replicate p.1 false,List.replicate p.2 false))

def firstScores (ps : List (ℕ × ℕ)) := ps.map (fun p => List.replicate p.1 false)
def secondScores (ps : List (ℕ × ℕ)) := ps.map (fun p => List.replicate p.2 false)

end SubexponentialSAT.SqrtLog.PackingProgram.Zip

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyMerge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Relocation of the concrete stream merger into the sequential controller ABI. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.Subexp

def mergeRegisters (i : Fin 8) : Fin 16 := i.castAdd 8
def mergePorts : Fin 14 → Fin 48 := ![0,12,1,2,3,4,5,6,7,13,14,17,15,16]
theorem mergeRegisters_injective : Function.Injective mergeRegisters := Fin.castAdd_injective _ _
theorem mergePorts_injective : Function.Injective mergePorts := by decide

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingWeightProgramBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed binary computation of the reciprocal-error packing coefficients.
Sources 0..3 hold n,s,M,r. Outputs 4,5 hold n²s² and 8M²r².
Ports 6,7 and 8..12 are temporary products and arithmetic scratch. -/
namespace SubexponentialSAT.SqrtLog.PackingWeightProgram

def work : Fin 5 ↪ Fin 13 where
  toFun i := ⟨i.val + 8, by omega⟩
  inj' := by intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp at this; omega

end SubexponentialSAT.SqrtLog.PackingWeightProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual native coefficient construction followed by stream weighting. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.Subexp

def weightPorts : Fin 13 → Fin 48 := ![20,21,22,23,15,16,1,2,3,4,5,6,7]
theorem weightPorts_injective : Function.Injective weightPorts := by decide

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

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

def downOutput (step : ℕ → List Bool → List Bool) : ℕ → List Bool → List Bool
  | 0, out => out
  | n + 1, out => downOutput step n (step n out)

def downBudget (cost : ℕ → ℕ) : ℕ → ℕ
  | 0 => 2
  | n + 1 => cost n + downBudget cost n + 2

theorem downBudget_le (cost : ℕ → ℕ) (n B : ℕ)
    (h : ∀ i, i < n → cost i ≤ B) : downBudget cost n ≤ n * (B + 2) + 2 := by
  induction n with
  | zero => simp [downBudget]
  | succ n ih =>
    have hn := h n (by omega)
    have ht := ih (fun i hi => h i (by omega))
    simp only [downBudget]
    nlinarith

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

open SubexponentialSAT
open SubexponentialSAT.Subexp

abbrev unary (n : ℕ) := List.replicate n true

def readStack : Fin 8 → Fin 11 := ![0,3,8,6,5,7,9,10]
theorem readStack_injective : Function.Injective readStack := by decide

end SubexponentialSAT.SqrtLog.PackingPrefixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingPrefixProgramRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingPrefixProgram

open SubexponentialSAT
open SubexponentialSAT.Subexp

def budget (h W : ℕ) : ℕ := 24 * h * W + 25 * h + 13 * W + 48

end SubexponentialSAT.SqrtLog.PackingPrefixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingPrefixProgramLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingPrefixProgram

open SubexponentialSAT

structure Ports (r s : ℕ) where
  register : Fin 3 → Fin r
  stack : Fin 11 → Fin s
  register_injective : Function.Injective register
  stack_injective : Function.Injective stack

end SubexponentialSAT.SqrtLog.PackingPrefixProgram

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
open SubexponentialSAT.Subexp

def prefixRegisters (i : Fin 3) : Fin 16 := i.castAdd 13
def prefixPorts : Fin 11 → Fin 48 := ![8,18,10,1,2,3,4,5,6,7,13]

theorem prefixRegisters_injective : Function.Injective prefixRegisters := Fin.castAdd_injective _ _
theorem prefixPorts_injective : Function.Injective prefixPorts := by decide

def prefixABI : PackingPrefixProgram.Ports 16 48 :=
  ⟨prefixRegisters,prefixPorts,prefixRegisters_injective,prefixPorts_injective⟩

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramPrepare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Stage the actual selected words and owner plans for the native layout
suffix. The incidence dimension is converted from its actual binary master. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.Subexp
open PackingLoaderProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

def dimensionPorts : Fin 14 ↪ Fin 64 :=
  ⟨![58,42,2,3,4,5,6,7,8,9,10,11,12,13],by decide⟩
def prepareCopies : List (Fin 64 × Fin 64) := [(61,25),(62,40),(53,41),(54,45)]

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.Subexp

def combinedExponent (dc db : ℕ) := max 1 (max dc db)
def combinedConstant (cc cb : ℕ) := cc+1100*(cb+2)

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationEmitProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native emission of the positive part of a shifted coefficient array.
The dimensions and the singleton support mask are runtime data. The constant
cell is consumed without emission; all later cells are framed, including zero
coefficients. No normalization or arithmetic oracle is used. -/
namespace SubexponentialSAT.SqrtLog.PerturbationEmitProgram
open SubexponentialSAT

def emitMap : Fin 3 → Fin 256 := ![222,228,217]

end SubexponentialSAT.SqrtLog.PerturbationEmitProgram


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native high-variable dispatch from original-coordinate mask/assignment
masters. The runtime index is233, and both source masters are retained. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT

def flagRegs : Fin 3 → Fin 16 := ![0,1,15]


end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyCoordinate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Per-coordinate physical composition. Original ambient variable IDs remain
unchanged throughout row loading, singleton support construction and emission. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT

def coordinateEmitScratch : List (Fin 256) := [120,221,222,223,224,225,226,227,228]

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end


