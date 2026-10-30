-- Prove2me | Definitions.Def_OAIQ081S018
-- name    : OAIQ081S018
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:24:35.653476+00:00
-- url     : https://prove2.me/theorems/148bc71c-a361-4890-9360-57b2792c3535
-- title:
--   Definitions bundle OAIQ081S018 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 113 declarations of OpenAI's Lean: 85 definitions, 1 inductive type or structure and 27 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssembly.Relational.FoldRel`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.NativePackingBounds.wordBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeTime.columnEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeTime.entryEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.dependencySet`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.energy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.incidenceReads`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.jointScore`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.singletonRead`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds.alphabetEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds.controllerEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds.coreEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds.extentEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds.loaderEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds.outputEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds.pairEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds.planEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds.prepareEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds.produceEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds.readyEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds.scoreEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds.seedEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds.selectionEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds.sourceEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds.suffixEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Store`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.cached`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates.low`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates.reg`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramPrefix.zipPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramPreserve.ports`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Boot.ports`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Boot.registers`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Emit.framePorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Emit.recordPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Install.ports`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Lift.ports`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Lift.registers`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Rows.ports`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Rows.registers` and 46 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_MomentsAssemblyFoldRel`, `SubexponentialSAT_SqrtLog_NativePackingBoundsTail`, `SubexponentialSAT_SqrtLog_NodeTimeColumns`, `SubexponentialSAT_SqrtLog_PackingCallerProgramBasic`, `SubexponentialSAT_SqrtLog_PackingCallerProgramBoundsBasic`, `SubexponentialSAT_SqrtLog_PackingCallerProgramBoundsCore`, `SubexponentialSAT_SqrtLog_PackingCallerProgramBoundsLoader`, `SubexponentialSAT_SqrtLog_PackingCallerProgramBoundsOutput`, `SubexponentialSAT_SqrtLog_PackingCallerProgramBoundsSelection`, `SubexponentialSAT_SqrtLog_PackingCallerProgramCache`, `SubexponentialSAT_SqrtLog_PackingHeadIdentity`, `SubexponentialSAT_SqrtLog_PackingHeadProgramCandidates`, `SubexponentialSAT_SqrtLog_PackingHeadProgramPrefix`, `SubexponentialSAT_SqrtLog_PackingHeadProgramPreserve`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputEmit`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputInstall`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputNative`, `SubexponentialSAT_SqrtLog_PackingIncidenceProgramInstall`, `SubexponentialSAT_SqrtLog_PackingLoaderProgramCapture`, `SubexponentialSAT_SqrtLog_PackingPrefix`, `SubexponentialSAT_SqrtLog_PackingPrefixProgram`, `SubexponentialSAT_SqrtLog_PackingPrefixScore`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyBounds`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyHeadSetup`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyHeads`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyRefinement`, `SubexponentialSAT_SqrtLog_PackingProgramEmit`, `SubexponentialSAT_SqrtLog_PackingSelection`, `SubexponentialSAT_SqrtLog_PackingVariance`, `SubexponentialSAT_SqrtLog_PackingWeightProgramGateBasic`, `SubexponentialSAT_SqrtLog_PackingWords`, `SubexponentialSAT_Subexp_ActivePlanProgram`, `SubexponentialSAT_Subexp_CandidateScoreProgram`, `SubexponentialSAT_Subexp_CandidateScoreRefinement`, `SubexponentialSAT_Subexp_CoefficientSearch`, `SubexponentialSAT_Subexp_CollisionGenerateProgram`, `SubexponentialSAT_Subexp_CollisionTupleProgram`, `SubexponentialSAT_Subexp_PackingExtractionBounds`, `SubexponentialSAT_Subexp_PaddedCompletion`, `SubexponentialSAT_Subexp_ReadPlan`, `SubexponentialSAT_Subexp_SelectionTableProgram`, `SubexponentialSAT_Subexp_SequentialStep`, `SubexponentialSAT_TypeDistribution`, `SubexponentialSAT_Variance`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S039`, `OAIQ081S040`, `OAIQ081S041` and `OAIQ081S043`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsAssemblyFoldRel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The execution-associated relational fold used by moment assembly. Keeping
this relation in its own module lets machine proofs depend on the relation
without importing the materializing moment-assembly programs. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssembly.Relational

inductive FoldRel {A W : Type*} (step : A → W → A → Prop) :
    List W → A → A → Prop
  | nil (a) : FoldRel step [] a a
  | cons {x xs a b c} : step a x b → FoldRel step xs b c → FoldRel step (x :: xs) a c

end OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssembly.Relational
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CoefficientSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable finite search for binomial interpolation coefficients

Execution uses an explicit residue alphabet, tuple enumeration, and equation
tests. The determinant-one interpolation theorem is used only to prove that
the search succeeds. No inverse or choice operator occurs in the algorithm.
-/

namespace SubexponentialSAT.Subexp.CoefficientSearch

open scoped BigOperators

section FiniteEnumeration

variable {α β : Type*}

/-- Enumerate all fixed-length tuples over a given finite alphabet. -/
def tuples (alphabet : List α) : (R : ℕ) → List (Fin R → α)
  | 0 => [fun i => Fin.elim0 i]
  | R + 1 =>
    let previous := tuples alphabet R
    alphabet.flatMap (fun a => previous.map (Fin.cons a))

end FiniteEnumeration

end SubexponentialSAT.Subexp.CoefficientSearch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Variance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A finite dependency-graph variance bound

All expectations below are finite rational sums. The main theorem expands the
square of a centered count into a double sum of covariances. Nonneighbors have
zero covariance; at most `d + 1` entries in each row remain, each at most one.
-/

namespace SubexponentialSAT.Variance

open scoped BigOperators

variable {Ω V U : Type*}

/-- Finite weighted expectation. Normalization is an explicit theorem hypothesis. -/
def mean [Fintype Ω] (weight : Ω → ℚ) (f : Ω → ℚ) : ℚ :=
  ∑ ω, weight ω * f ω

section Mean

variable [Fintype Ω] (weight : Ω → ℚ)

/-- Equal weights on a finite outcome space. -/
def uniformWeight (_ω : Ω) : ℚ := 1 / (Fintype.card Ω : ℚ)

/-- Bridge to the ordinary sum-divided-by-cardinality finite average. -/
theorem mean_uniformWeight (f : Ω → ℚ) :
    mean uniformWeight f = (∑ ω, f ω) / (Fintype.card Ω : ℚ) := by
  simp only [mean, uniformWeight, ← Finset.mul_sum]
  ring

end Mean

end SubexponentialSAT.Variance

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_TypeDistribution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Uniform words induce uniform local types

The outcome space consists of all assignments of words to distinct factor,
head, and padding indices. Local read maps are injective. Read maps at
distinct coordinates sharing no factor have disjoint ranges. Finite product
counting then supplies the actual marginals and pair moments needed by
SubexponentialSAT.Variance; these probabilistic properties are conclusions, not hypotheses.
-/

namespace SubexponentialSAT.TypeDistribution

open scoped BigOperators
open SubexponentialSAT.Variance

section FiniteMeans

variable {A B I J W : Type*}

theorem mean_equiv [Fintype A] [Fintype B] (e : A ≃ B) (f : B → ℚ) :
    mean uniformWeight (fun a => f (e a)) = mean uniformWeight f := by
  rw [mean_uniformWeight, mean_uniformWeight, e.sum_comp, Fintype.card_congr e]

theorem mean_prod_fst [Fintype A] [Fintype B] [Nonempty B] (f : A → ℚ) :
    mean uniformWeight (fun p : A × B => f p.1) = mean uniformWeight f := by
  have hb : (Fintype.card B : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [mean_uniformWeight, mean_uniformWeight, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum,
    Fintype.card_prod, Nat.cast_mul]
  rw [mul_comm (Fintype.card A : ℚ) (Fintype.card B : ℚ)]
  exact mul_div_mul_left _ _ hb

theorem mean_indicator [Fintype A] [DecidableEq A] (u : A) :
    mean uniformWeight (fun a : A => if a = u then (1 : ℚ) else 0) =
      1 / (Fintype.card A : ℚ) := by
  rw [mean_uniformWeight]
  simp

/-- Coordinates outside the image of an injective read map. -/
abbrev Unread (e : J ↪ I) := {i : I // i ∉ Set.range e}

/-- Split a global assignment into the read coordinates and all remaining ones. -/
noncomputable def splitReads (e : J ↪ I) (W : Type*) :
    (I → W) ≃ (J → W) × (Unread e → W) := by
  classical
  exact (Equiv.piEquivPiSubtypeProd (fun i => i ∈ Set.range e) (fun _ => W)).trans
    (Equiv.prodCongr
      (Equiv.arrowCongr (Equiv.ofInjective e e.injective).symm (Equiv.refl W))
      (Equiv.refl _))

@[simp] theorem splitReads_fst (e : J ↪ I) (ω : I → W) :
    (splitReads e W ω).1 = fun j => ω (e j) := rfl

/-- Restricting independent uniform coordinates along an injection is uniform. -/
theorem mean_restrict [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype W] [Nonempty W]
    (e : J ↪ I) (f : (J → W) → ℚ) :
    mean uniformWeight (fun ω : I → W => f (fun j => ω (e j))) =
      mean uniformWeight f := by
  classical
  calc
    _ = mean uniformWeight (fun p : (J → W) × (Unread e → W) => f p.1) :=
      mean_equiv (splitReads e W) _
    _ = _ := mean_prod_fst f

end FiniteMeans

end SubexponentialSAT.TypeDistribution

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PaddedCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Explicit padded completion leaves

Every optional coordinate branches over the entire word alphabet. A real
coordinate updates the assignment; a dummy coordinate ignores the word.
Padding therefore implements the common-denominator multiplicity by actual
finite leaves rather than a multiplication of the resulting score.
-/

namespace SubexponentialSAT.Subexp.PaddedCompletion

variable {I W J : Type*} [DecidableEq I]

/-- Real coordinates update the assignment; dummy coordinates consume a
choice without changing it. -/
def assignOptional (ω : I → W) (i : Option I) (w : W) : I → W :=
  match i with
  | none => ω
  | some j => Function.update ω j w

/-- Actual finite generation of collision Booleans, including every dummy
choice. No arithmetic scaling is used by this executable definition. -/
def leaves (alphabet : List W) (f : (I → W) → Bool) :
    List (Option I) → (I → W) → List Bool
  | [], ω => [f ω]
  | i :: remaining, ω =>
    alphabet.flatMap (fun w => leaves alphabet f remaining (assignOptional ω i w))

/-- Append enough ignored coordinates to reach the common support bound. -/
def paddedIndices (remaining : List I) (S : ℕ) : List (Option I) :=
  remaining.map some ++ List.replicate (S - remaining.length) none

def paddedLeaves (alphabet : List W) (f : (I → W) → Bool)
    (remaining : List I) (S : ℕ) (ω : I → W) : List Bool :=
  leaves alphabet f (paddedIndices remaining S) ω

theorem sum_map_const {α : Type*} (as : List α) (n : ℕ) :
    (as.map (fun _ => n)).sum = as.length * n := by
  induction as with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    rw [Nat.succ_mul, Nat.add_comm]

omit [DecidableEq I] in
theorem paddedIndices_length (remaining : List I) (S : ℕ)
    (hS : remaining.length ≤ S) : (paddedIndices remaining S).length = S := by
  simp only [paddedIndices, List.length_append, List.length_map, List.length_replicate]
  exact Nat.add_sub_of_le hS

end SubexponentialSAT.Subexp.PaddedCompletion

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

section Gather

variable {W : Type*}

theorem getD_map_of_lt {A B : Type*} (f : A → B) (xs : List A)
    (a : A) (b : B) (n : ℕ) (hn : n < xs.length) :
    (xs.map f).getD n b = f (xs.getD n a) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hn), List.getD_eq_getElem _ _ hn]
  simp

end Gather

section PartialAssignments

variable {W : Type*}

/-- A free seed reads its candidate-tuple position after the current array;
every other seed keeps its original current-array position. -/
def selectPosition (currentSize : ℕ) (remaining : List ℕ) (n : ℕ) : ℕ :=
  if n ∈ remaining then currentSize + remaining.idxOf n else n

def completionPlan (currentSize : ℕ) (remaining plan : List ℕ) : List ℕ :=
  plan.map (selectPosition currentSize remaining)

def completedAt (default : W) (current : List W) (remaining : List ℕ)
    (candidate : List W) (n : ℕ) : W :=
  if n ∈ remaining then candidate.getD (remaining.idxOf n) default
  else current.getD n default

@[simp] theorem completionPlan_length (currentSize : ℕ) (remaining plan : List ℕ) :
    (completionPlan currentSize remaining plan).length = plan.length := by
  simp [completionPlan]

/-- The optional-coordinate update semantics used by the padded leaf tree,
driven by one explicit list of candidate words. -/
def applyChoices (current : ℕ → W) : List (Option ℕ) → List W → ℕ → W
  | [], _ => current
  | _ :: _, [] => current
  | i :: remaining, w :: candidate =>
      applyChoices (PaddedCompletion.assignOptional current i w) remaining candidate

theorem applyChoices_none (current : ℕ → W) (padding : ℕ) (candidate : List W) :
    applyChoices current (List.replicate padding none) candidate = current := by
  induction padding generalizing current candidate with
  | zero => rfl
  | succ padding ih =>
    cases candidate with
    | nil => rfl
    | cons w candidate =>
      simpa [List.replicate_succ, applyChoices, PaddedCompletion.assignOptional] using
        (ih current candidate)

theorem applyChoices_padding (current : ℕ → W) (remaining : List ℕ)
    (padding : ℕ) (candidate : List W) :
    applyChoices current (remaining.map some ++ List.replicate padding none) candidate =
      applyChoices current (remaining.map some) candidate := by
  induction remaining generalizing current candidate with
  | nil => simpa [applyChoices] using applyChoices_none current padding candidate
  | cons i remaining ih =>
    cases candidate with
    | nil => rfl
    | cons w candidate =>
      simpa only [List.map_cons, List.cons_append, applyChoices] using
        ih (PaddedCompletion.assignOptional current (some i) w) candidate

theorem applyChoices_real (default : W) (current : ℕ → W)
    (remaining : List ℕ) (candidate : List W) (hn : remaining.Nodup)
    (hlen : remaining.length ≤ candidate.length) (n : ℕ) :
    applyChoices current (remaining.map some) candidate n =
      if n ∈ remaining then candidate.getD (remaining.idxOf n) default else current n := by
  induction remaining generalizing current candidate with
  | nil => simp [applyChoices]
  | cons i remaining ih =>
    cases candidate with
    | nil => simp at hlen
    | cons w candidate =>
      have ht : remaining.length ≤ candidate.length := by simpa using hlen
      simp only [List.map_cons, applyChoices]
      rw [ih _ _ hn.of_cons ht]
      by_cases hni : n = i
      · subst n
        have hi : i ∉ remaining := (List.nodup_cons.mp hn).1
        simp [hi, PaddedCompletion.assignOptional]
      · simp [hni, Ne.symm hni, PaddedCompletion.assignOptional, Function.update_of_ne]

/-- Each actual leaf is obtained by one explicit tuple in the same recursive
order as the padded completion tree. -/
theorem leaves_eq_tuples (alphabet : List W) (f : (ℕ → W) → Bool)
    (remaining : List (Option ℕ)) (current : ℕ → W) :
    PaddedCompletion.leaves alphabet f remaining current =
      (CoefficientSearch.tuples alphabet remaining.length).map
        (fun candidate => f (applyChoices current remaining (List.ofFn candidate))) := by
  induction remaining generalizing current with
  | nil => simp [PaddedCompletion.leaves, CoefficientSearch.tuples, applyChoices]
  | cons i remaining ih =>
    simp only [PaddedCompletion.leaves, List.length_cons, CoefficientSearch.tuples,
      List.map_flatMap]
    apply congrArg (fun g => alphabet.flatMap g)
    funext w
    rw [ih]
    simp only [List.map_map]
    congr 1
    funext candidate
    simp [ List.ofFn_succ, applyChoices]

end PartialAssignments

end SubexponentialSAT.Subexp.ReadPlan

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

theorem slice_flatten (rows : List (List Bool)) (width : ℕ)
    (hrows : ∀ row ∈ rows, row.length = width) (i : ℕ) :
    (rows.flatten.drop (i * width)).take width = rows.getD i [] := by
  induction rows generalizing i with
  | nil => simp
  | cons row rows ih =>
    have hr := hrows row (by simp)
    have ht : ∀ r ∈ rows, r.length = width := fun r h => hrows r (by simp [h])
    cases i with
    | zero => simpa using (List.take_left' (l₁ := row) (l₂ := rows.flatten) hr)
    | succ i =>
      have hm : (i + 1) * width = row.length + i * width := by rw [hr]; ring
      rw [List.flatten_cons, hm, ← List.drop_drop, List.drop_left]
      simpa using ih ht i

end SubexponentialSAT.Subexp.CollisionTupleProgram

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

def generatorPorts : Fin 9 → Fin 20 := ![16, 19, 2, 4, 5, 6, 7, 8, 17]

end SubexponentialSAT.Subexp.CollisionGenerateProgram

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

def lowStacks (i : Fin 26) : Fin 36 := Fin.castAdd 10 i

def writerRegisters : Fin 3 → Fin 16 := ![0,1,2]
def writerStacks : Fin 2 → Fin 36 := ![18,35]

end SubexponentialSAT.Subexp.CandidateScoreProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_NativePackingBoundsTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Bounds for the actual packing tail

All sizes below come from the represented input and generated records.
There is no assumed runtime certificate: the cost estimates apply to the
same leftover and inverse budgets used by `PackingExecution.program_trace`.
-/

namespace SubexponentialSAT.SqrtLog.NativePackingBounds

open SubexponentialSAT.Subexp

variable {U : Type*} [DecidableEq U]

def wordBound (D : ℕ) : ℕ := 1 + (2 * D + 2) * D

end SubexponentialSAT.SqrtLog.NativePackingBounds

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

def recordPorts : Fin 4 → Fin 6 := ![0,4,3,2]

def framePorts : Fin 3 → Fin 6 := ![3,2,5]
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Emit

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact collision-energy bounds used in correlated incidence packing. -/
namespace SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators
open SubexponentialSAT.Variance

noncomputable section

variable {Ω I U : Type*} [Fintype Ω] [Fintype I] [Fintype U]
  [DecidableEq I] [DecidableEq U] [Nonempty Ω] [Nonempty U]

/-- Sum of squared deviations of the actual type counts. -/
def energy (label : I → U) : ℚ :=
  ∑ u, (((Finset.univ.filter fun i => label i = u).card : ℚ) -
    (Fintype.card I : ℚ) / (Fintype.card U : ℚ)) ^ 2

end
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual shared-head/shared-factor words on an arbitrary finite incidence set. -/
namespace SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators
open SubexponentialSAT.Variance

noncomputable section

section Evaluation
variable {J W : Type*} [Fintype J] [DecidableEq J] [Fintype W] [Nonempty W]

def singletonRead (j : J) : Unit ↪ J := ⟨fun _ => j, fun _ _ _ => Subsingleton.elim _ _⟩

theorem mean_eval (j : J) (F : W → ℚ) :
    mean uniformWeight (fun ω : J → W => F (ω j)) = mean uniformWeight F := by
  calc
    _ = mean uniformWeight (fun ξ : Unit → W => F (ξ ())) :=
      SubexponentialSAT.TypeDistribution.mean_restrict (singletonRead j) _
    _ = _ := SubexponentialSAT.TypeDistribution.mean_equiv (Equiv.funUnique Unit W) F

end Evaluation

section Incidences
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

def incidenceReads (i : I) : Bool ↪ (V ⊕ E) where
  toFun b := if b then .inr (factor i) else .inl (ivar i)
  inj' := by intro b c h; cases b <;> cases c <;> simp_all

def dependencySet (i : I) : Finset I :=
  Finset.univ.filter fun j => ivar j = ivar i ∨ factor j = factor i

end Incidences
end
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Simultaneous type packing and original-variable head balance. -/
namespace SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators
open SubexponentialSAT.Variance
noncomputable section

section Joint
variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-- A denominator-free joint score; only rational arithmetic is needed. -/
def jointScore (X Y : Ω → ℚ) (x y : ℚ) (ω : Ω) : ℚ :=
  y^2 * X ω + x^2 * Y ω

end Joint

end
end SubexponentialSAT.SqrtLog.Packing

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

def active (seeds plan : List ℕ) (fixedCount : ℕ) : List ℕ :=
  seeds.filter (fun n => decide (fixedCount ≤ n ∧ n ∈ plan))

@[simp] theorem mem_active (seeds plan : List ℕ) (fixedCount n : ℕ) :
    n ∈ active seeds plan fixedCount ↔ n ∈ seeds ∧ fixedCount ≤ n ∧ n ∈ plan := by
  simp [active ]

/-- Filtering the complete ascending seed enumeration is exactly filtering
the unprocessed suffix range; no sorting or deduplication is assumed. -/
theorem active_range_eq (seedCount fixedCount : ℕ) (plan : List ℕ) :
    active (List.range seedCount) plan fixedCount =
      (List.range' fixedCount (seedCount - fixedCount)).filter (fun n => decide (n ∈ plan)) := by
  have hleft : List.Pairwise (· < ·) (active (List.range seedCount) plan fixedCount) :=
    List.Pairwise.filter _ List.pairwise_lt_range
  have hrange : List.Pairwise (· < ·) (List.range' fixedCount (seedCount - fixedCount)) :=
    List.pairwise_lt_range'
  apply List.Pairwise.eq_of_mem_iff hleft (List.Pairwise.filter _ hrange)
  intro n
  by_cases hp : n ∈ plan
  · simp [mem_active, List.mem_filter, List.mem_range'_1, hp]
    omega
  · simp [mem_active, List.mem_filter, List.mem_range'_1, hp]

end SubexponentialSAT.Subexp.ActivePlanProgram

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

def unary (n : ℕ) : List Bool := List.replicate n true

end SubexponentialSAT.Subexp.SelectionTableProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CandidateScoreRefinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Candidate-array and generated-score refinement

The concrete temporary array has the same values as the search decoder after
one candidate is prepended. Generated collision streams may be permuted;
their successful-leaf counts still equal the exact natural evaluator.
-/

namespace SubexponentialSAT.Subexp.CandidateScoreRefinement

theorem map_range_getD {A : Type*} (default : A) (M : ℕ) (xs : List A)
    (h : xs.length ≤ M) :
    (List.range M).map (fun i => xs.getD i default) =
      xs ++ List.replicate (M - xs.length) default := by
  induction M generalizing xs with
  | zero =>
      have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
      simp [hx]
  | succ M ih =>
      cases xs with
      | nil => simp
      | cons x xs =>
          have hh := ih xs (by simpa using h)
          simpa [List.range_succ_eq_map, List.map_map, Function.comp_def] using
            congrArg (List.cons x) hh

end SubexponentialSAT.Subexp.CandidateScoreRefinement

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

def minimumBudget (q S : ℕ) : ℕ := 500 * (q * (S + 1)) ^ 2
def recordBudget (q S : ℕ) : ℕ := 2 * (q * S) + 2 * q + 1
def updateBudget (q total width : ℕ) : ℕ :=
  (q * (14 * width + 10) + 15 * width + 16) +
    ((7 * total + 5) + (total * (14 * width + 10) + 20 * width + 21))
def selectionBudget (q S total width : ℕ) : ℕ :=
  9 + minimumBudget q S + updateBudget q total width +
    9 * (2 * (recordBudget q S + minimumBudget q S + width) + 3) + 2

end SubexponentialSAT.Subexp.SequentialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputNative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! Convert a physically scanned factor-index stream to incidence plans. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Rows
open SubexponentialSAT.Subexp

abbrev unary (n : ℕ) := List.replicate n true

def registers : Fin 3 → Fin 6 := Fin.castAdd 3
def ports : Fin 6 → Fin 9 := ![0,3,4,5,6,7]
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Rows


/-! Native per-variable incident-factor scan from the original scope stream. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Scan
open SubexponentialSAT.Subexp

def registers : Fin 10 → Fin 16 := Fin.castAdd 6
def ports : Fin 10 → Fin 32 := Fin.castAdd 22
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Scan


/-! Fixed cleanup for the native scope-address scanner. -/


/-! Calls to the fixed record mapper inside the native scope scan. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Lift
open SubexponentialSAT.Subexp
def registers : Fin 6 → Fin 16 := Fin.castAdd 10
def ports : Fin 9 → Fin 32 := ![22,21,12,13,14,15,16,25,7]
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Lift


/-! One native low-variable step, including its uncovered neutral factor. -/


/-! Runtime high-mask loop for the original-address incidence stream. -/


/-! Count the physical scope stream before constructing native incidence plans. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Boot
open SubexponentialSAT.Subexp
def registers : Fin 2 → Fin 16 := Fin.castAdd 14
def ports : Fin 2 → Fin 32 := ![0,24]
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Boot

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingHeadIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One-hot word overlap is exactly the number of equal head coordinates. -/
namespace SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators

theorem zipWith_ofFn' {A B C : Type*} (op : A → B → C) {n : ℕ}
    (f : Fin n → A) (g : Fin n → B) :
    List.zipWith op (List.ofFn f) (List.ofFn g) = List.ofFn (fun i => op (f i) (g i)) := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.ofFn_succ, ih]

theorem count_true_ofFn {n : ℕ} (f : Fin n → Bool) :
    (List.ofFn f).count true = ∑ i, if f i then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ, List.count_cons, Fin.sum_univ_succ, ih]
    cases f 0 <;> simp [Nat.add_comm]

end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Heads-first numbering and the actual reverse-list assignment prefix. -/
namespace SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators

section Enumeration
variable {A B R : Type*} [DecidableEq A] [DecidableEq B]

theorem prefix_enumeration_sum [Fintype A] [AddCommMonoid R]
    (xs : List A) (hn : xs.Nodup) (hf : ∀ x, x ∈ xs) (f : A → R) :
    (xs.map f).sum = ∑ x, f x := by
  rw [← List.sum_toFinset f hn]
  have heq : xs.toFinset = Finset.univ := by ext x; simp [hf x]
  rw [heq]
end Enumeration

section Decoding
variable {W : Type*}

theorem prefix_not_remaining (fixed : List W) (n i : ℕ) (hi : i ≤ fixed.length) :
    i ∉ List.range' (fixed.length + 1) n := by
  simp only [List.mem_range']
  omega
end Decoding

end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_NodeTimeColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.NodeTime
open SubexponentialSAT Subexp

def entryEnvelope (X : ℕ) : ℕ :=
  800*(2*X+1)^2+1+10000000000000*(X+1)^5+550*(X*X+11*X+1)+450*(100*(X+1)^2)+1200

def columnEnvelope (X : ℕ) : ℕ :=
  1000*(2*X+1)^2+18*X+2*X+39+
    X*(entryEnvelope X+5*X+12+25000*((X+1)*(100*(X+1)^2+2)+3)^2+9*(100*(X+1)^2+2))

end SubexponentialSAT.SqrtLog.NodeTime

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceProgramInstall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid generation and installation of raw pairs from a linear plan stream. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceProgram.Install
open SubexponentialSAT.Subexp

def registers : Fin 10 → Fin 16 := Fin.castAdd 6
def ports : Fin 9 → Fin 48 := ![0,20,21,22,23,24,25,26,27]
def bank : List (Fin 48) := [20,21,22,23,24,25,26,27]

end SubexponentialSAT.SqrtLog.PackingIncidenceProgram.Install

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputInstall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Raw scope bytes and a mask produce the actual installed incidence-pair table. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Install
open SubexponentialSAT.Subexp

def ports (i : Fin 32) : Fin 48 :=
  if i=20 then 32 else if i=21 then 33 else if i=22 then 34
  else if i=24 then 35 else if i=25 then 20 else if i=26 then 36 else i.castAdd 16
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Install

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

def captureBudget (scopeBits n k f : ℕ) := 9*scopeBits+9*n+2*k+9*f+27

/- The full ambient count is retained; the factor prefix never uses the
free-variable count. Scopes are physically copied to master60 before cleanup. -/

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Framed local storage for the concrete packing caller. Ports53/54 retain
width/alphabet,55..59 parameters,60 scopes,61 plans,62 words,63 metadata. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open PackingLoaderProgram
abbrev Store := Fin 64 → List Bool

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingExtractionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial bounds for the actual nested complete-block extraction. -/

namespace SubexponentialSAT.Subexp.PackingExtraction

def unitBudget (B I A : ℕ) : ℕ := 106 * B + 100 * I + 100 * A + 207

end SubexponentialSAT.Subexp.PackingExtraction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramCache
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open PackingLoaderProgram

def cached (outside : Store) (width alphabet : List Bool) : Store :=
  Function.update (Function.update outside 53 width) 54 alphabet

@[simp] theorem cached_52 (outside : Store) (width alphabet : List Bool) :
    cached outside width alphabet 52=outside 52 := by simp [cached]
@[simp] theorem cached_width (outside : Store) (width alphabet : List Bool) :
    cached outside width alphabet 53=width := by simp [cached]
@[simp] theorem cached_alphabet (outside : Store) (width alphabet : List Bool) :
    cached outside width alphabet 54=alphabet := by simp [cached]

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingPrefixScore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact head-term enumeration and physical prefix overlap. -/
namespace SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators

theorem prefix_sum_flatMap {A R : Type*} [AddMonoid R]
    (xs : List A) (f : A → List R) :
    (xs.flatMap f).sum = (xs.map (fun x => (f x).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

end SubexponentialSAT.SqrtLog.Packing

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

def zipPorts : Fin 3 → Fin 6 := ![2,1,4]

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

def ports : Fin 6 → Fin 8 := ![0,6,2,3,4,7]

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

def reg (i : Fin 3) : Fin 8 := i.castAdd 5
def writerStack : Fin 2 → Fin 12 := ![4,9]

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

def reg (i : Fin 5) : Fin 8 := i.castAdd 3
def low (i : Fin 8) : Fin 12 := i.castAdd 4

end SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates

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

def normStack (out : Fin 11) : Fin 2 → Fin 11 := ![5,out]

def mulStack : Fin 7 → Fin 11 := ![8,2,9,10,6,5,7]

end SubexponentialSAT.SqrtLog.PackingPrefixProgram

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

def unaryRegisters : Fin 3 → Fin 4 := Fin.castAdd 1
def unaryStacks : Fin 3 → Fin 7 := ![3,4,6]

def compareStacks : Fin 2 → Fin 7 := ![4,5]

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
open SubexponentialSAT.Subexp

def gateRegisters (i : Fin 4) : Fin 16 := i.castAdd 12
def gatePorts : Fin 7 → Fin 48 := ![20,19,18,1,2,3,4]

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
open SubexponentialSAT.Subexp

def headRegisters (i : Fin 8) : Fin 16 := i.castAdd 8

def headPorts : Fin 12 → Fin 48 := ![3,1,4,5,6,2,7,13,14,12,15,16]

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Numerical closure for the fixed packing scorer.  Every argument of the
bound is an input size or a numeric weight; no running-time oracle occurs. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.Subexp

def headBudgetBound (total q wordWidth heads L : ℕ) : ℕ :=
  80*(heads+total+L+1)^2+1+
  (24*total*wordWidth+25*total+13*wordWidth+48)+1+
  (7*(1+(2*wordWidth+2)*q)+5)+16+
  (q*(43*total*wordWidth+20*total+17*wordWidth+66)+22)+
  3*(2*(total*wordWidth+total)+3)

def uniformBudget (total pairs raw q wordWidth heads W L : ℕ) : ℕ :=
  let C := pairs*q^4+total*wordWidth
  10000*31^6*(32*(total+raw+q+wordWidth+1)^2+1)^12*q^4+
  12*L+48+headBudgetBound total q wordWidth heads L+
  500*(2*L+4)^2+1+
  500*(q+1)*(W+1)*(2*L+6+C+1)+
  6*(q*(4*W*C+2)+1)+4*(2*L+6)+14

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyRefinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The complete fixed producer discharges the sequential controller ABI. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.Subexp

def parameterBits (nb sb mb rb : List Bool) : ℕ := nb.length+sb.length+mb.length+rb.length

def magnitude (heads s M r : ℕ) : ℕ := heads^2*s^2+8*M^2*r^2

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramBoundsBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds
open SubexponentialSAT.Subexp
open PackingLoaderProgram PackingIncidenceInput

def planEnvelope (S : ℕ) := 1+(16*(2*S)+24)*S
def pairEnvelope (S : ℕ) := 1+(32*(2*S+1)+14)*S^2
def alphabetEnvelope (S : ℕ) := 1+(2*S^2+2)*S
def seedEnvelope (S : ℕ) := 1+(2*(2*S)+2)*(2*S)
def extentEnvelope (S : ℕ) :=
  1+S+S+0+S+S+1+2+S^2+2*S+S+(1+(2*S+2)*S)+
  alphabetEnvelope S+S^2+S*S^2+seedEnvelope S+pairEnvelope S

def sourceEnvelope (S : ℕ) :=
  S+1+S+S^2+(2*S)*S^2+alphabetEnvelope S+planEnvelope S+1

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramBoundsLoader
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds
open SubexponentialSAT.Subexp
open PackingLoaderProgram PackingIncidenceInput

attribute [local simp] Fin.coe_ofNat_eq_mod

def loaderEnvelope (S : ℕ) := 22000*(extentEnvelope S+11*S+1)^4
def readyEnvelope (S : ℕ) := (2*S)*extentEnvelope S+extentEnvelope S+4*S+4

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramBoundsSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds
open SubexponentialSAT.Subexp
open PackingLoaderProgram PackingIncidenceInput

def scoreEnvelope (S : ℕ) := (S*S)^2*(S^2*S^4)+8*(S*S)^2*((2*S)*S^2)
def controllerEnvelope (S : ℕ) :=
  (2*S)*(PackingProgram.Assembly.uniformBudget (2*S) (S^2) (S^2) S (S^2) S
    (S^2*S^2+8*S^2*S^2) (4*S)+
      SequentialProgram.selectionBudget S (scoreEnvelope S) (2*S) (S^2)+3)+3

def selectionEnvelope (S : ℕ) :=
  7*readyEnvelope S+5+(7*readyEnvelope S+5)+controllerEnvelope S+
    (7*((2*S)*S^2)+5)+48*(2*(48*readyEnvelope S+(2*S)*S^2+2*S+1)+3)

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramBoundsCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds
open SubexponentialSAT.Subexp
open PackingLoaderProgram PackingIncidenceInput
attribute [local simp] Fin.coe_ofNat_eq_mod

def produceEnvelope (S : ℕ) :=
  4000*(3*S+1)^3+1+(7*planEnvelope S+5)+
    (4+100*(2400*(S+1)^2*(24*(2*S)+34)+11+(16*(2*S)+24)*S))
def prepareEnvelope (S : ℕ) :=
  7*S+6+32*(S+1)*(S+1)+1+4+
    7*(planEnvelope S+(2*S)*S^2+S^2+alphabetEnvelope S)+20
def suffixEnvelope (S : ℕ) := prepareEnvelope S+81000000*sourceEnvelope S^12+
  (7*(34*sourceEnvelope S^4)+5)+48*(2*(34*sourceEnvelope S^4)+3)
def coreEnvelope (S : ℕ) :=
  produceEnvelope S+loaderEnvelope S+selectionEnvelope S+suffixEnvelope S

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramBoundsOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds
open SubexponentialSAT.Subexp
open PackingLoaderProgram PackingIncidenceInput
attribute [local simp] Fin.coe_ofNat_eq_mod

def outputEnvelope (S : ℕ) :=
  S+S^2+alphabetEnvelope S+planEnvelope S+(2*S)*S^2+34*sourceEnvelope S^4

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds

end OAI.Algorithms
end


