-- Prove2me | Definitions.Def_OAIQ081S112
-- name    : OAIQ081S112
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:26:56.911023+00:00
-- url     : https://prove2.me/theorems/4fa9acd3-0b4c-44ef-8566-9fbd848f0c0a
-- title:
--   Definitions bundle OAIQ081S112 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 20 declarations of OpenAI's Lean: 6 definitions and 14 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadIncremental.physicalOverlap`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadIncremental.sequentialHeadCount`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadIncremental.sequentialIncidenceCount`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceProgram.incidenceNumerator`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.candidateScore`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram.Data`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: [`SubexponentialSAT_SqrtLog_PackingHeadIncrementalCounts`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingHeadIncrementalCounts.lean), [`SubexponentialSAT_SqrtLog_PackingHeadIncrementalPhysical`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingHeadIncrementalPhysical.lean), [`SubexponentialSAT_SqrtLog_PackingHeadIncrementalSequential`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingHeadIncrementalSequential.lean), [`SubexponentialSAT_SqrtLog_PackingHeadIncrementalWeighted`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingHeadIncrementalWeighted.lean), [`SubexponentialSAT_SqrtLog_PackingIncidenceProgramRefinement`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingIncidenceProgramRefinement.lean), [`SubexponentialSAT_SqrtLog_PackingLoaderProgramFrame`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingLoaderProgramFrame.lean), [`SubexponentialSAT_SqrtLog_PackingProgramAssemblyHeads`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingProgramAssemblyHeads.lean), [`SubexponentialSAT_SqrtLog_PackingProgramAssemblyOrder`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingProgramAssemblyOrder.lean), [`SubexponentialSAT_SqrtLog_PackingProgramAssemblyScore`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingProgramAssemblyScore.lean), [`SubexponentialSAT_SqrtLog_PackingProgramCounts`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingProgramCounts.lean), [`SubexponentialSAT_SqrtLog_SquarefreeKeyMapProgram`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/SquarefreeKeyMapProgram.lean).
--
--   **Imports.** It imports the bundles `OAIQ081S084`, `OAIQ081S085`, `OAIQ081S089`, `OAIQ081S093`, `OAIQ081S096` and `OAIQ081S097` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S132`, `OAIQ081S133` and `OAIQ081S135`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ081S084
import Definitions.Def_OAIQ081S085
import Definitions.Def_OAIQ081S089
import Definitions.Def_OAIQ081S093
import Definitions.Def_OAIQ081S096
import Definitions.Def_OAIQ081S097

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramCounts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Splitting all weighted completions into two unweighted integer counts. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram
open SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp.LocalExpectation
open SubexponentialSAT.SqrtLog.Packing SubexponentialSAT.MulticolorTypes

section Scores
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] [DecidableEq V] [DecidableEq E] in
theorem naturalTerm_split (w : Weights) (z : ScoreTerm I V Q)
    (ω : WordAssignment V E r Q) :
    naturalTerm ivar factor w z ω =
      w.incidence * incidenceIndicator ivar factor z ω + w.head * headIndicator z ω := by
  cases z with
  | inl p => rcases p with ⟨i,j⟩; simp only [naturalTerm, incidenceIndicator, headIndicator]; split_ifs <;> simp
  | inr p => rcases p with ⟨t,v,u⟩; simp only [naturalTerm, incidenceIndicator, headIndicator]; split_ifs <;> simp

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem numerator_split (alphabet : List (Word r Q)) (terms : List (ScoreTerm I V Q))
    (indices : List (V ⊕ E)) (w : Weights) (remaining : List ℕ) (ω : ℕ → Word r Q) :
    numerator ivar factor alphabet terms indices w remaining ω =
      w.incidence * (unweightedCounts ivar factor alphabet terms indices remaining ω).1 +
      w.head * (unweightedCounts ivar factor alphabet terms indices remaining ω).2 := by
  unfold numerator numberedTerm
  simp_rw [naturalTerm_split]
  exact commonNumerator_linear _ _ _ _ _ _ _ _ _ _

end Scores
end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingHeadIncrementalCounts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

section Numbered
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem numbered_head_pair (alphabet : List (Word r Q)) (indices : List (V ⊕ E))
    (remaining : List ℕ) (ω : ℕ → Word r Q) (t : Fin Q) (v u : V) :
    scaledCount alphabet
      (fun η => PackingProgram.headIndicator (Sum.inr (t,v,u) : ScoreTerm I V Q)
        (fun i => η (indexCode indices i)))
      (numberedScoreSupport ivar factor indices (Sum.inr (t,v,u))) 4 remaining ω =
    pairCount alphabet remaining t (indexCode indices (Sum.inl v))
      (indexCode indices (Sum.inl u)) ω := by
  simp [pairCount, PackingProgram.headIndicator, numberedScoreSupport, scoreSupport]

omit [Fintype I] [Fintype E] [DecidableEq I] in
theorem unweighted_head_eq (alphabet : List (Word r Q)) (pairs : List (I × I))
    (vertices : List V) (hvN : vertices.Nodup) (hvC : ∀ v, v ∈ vertices)
    (indices : List (V ⊕ E)) (remaining : List ℕ) (ω : ℕ → Word r Q) :
    (PackingProgram.unweightedCounts ivar factor alphabet
      (pairs.map Sum.inl ++ headTerms (I := I) (Q := Q) vertices)
      indices remaining ω).2 =
      headCount alphabet (fun v : V => indexCode indices (Sum.inl v)) remaining ω := by
  simp only [PackingProgram.unweightedCounts, commonNumerator, List.map_append,
    List.sum_append, List.map_map, Function.comp_def]
  have hzero : (pairs.map (fun p => scaledCount alphabet
      (fun η => PackingProgram.headIndicator (Sum.inl p : ScoreTerm I V Q)
        (fun i => η (indexCode indices i)))
      (numberedScoreSupport ivar factor indices (Sum.inl p : ScoreTerm I V Q)) 4 remaining ω)).sum = 0 := by
    simp [scaledCount, PackingProgram.headIndicator, completionCount_zero]
  rw [hzero, zero_add]
  change ((headScoreTerms vertices Q).map _).sum = _
  rw [headScoreTerms_sum vertices hvN hvC]
  simp only [numbered_head_pair ivar factor, headCount]

end Numbered
end SubexponentialSAT.SqrtLog.PackingHeadIncremental

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

def sequentialHeadCount (alphabet : List (Word r Q)) (pairs : List (I × I))
    (vertices : List V) (factors : List E) (default : Word r Q)
    (n : ℕ) (fixed : List (Word r Q)) : ℕ :=
  (PackingProgram.unweightedCounts ivar factor alphabet
    (pairs.map Sum.inl ++ headTerms (I := I) (Q := Q) vertices)
    (headsFirstIndices vertices factors) (List.range' fixed.length n)
    (decode default fixed)).2

omit [Fintype I] [Fintype E] [DecidableEq I] in
/-- The exact factor is two times q^4, where q is the word-alphabet length.
The prefix is the actual reversed fixed-word store; its order does not affect
the sum. The common constant is not an input to the physical scorer. -/
theorem sequentialHead_decomposition
    (alphabet : List (Word r Q)) (haN : alphabet.Nodup) (haC : ∀ w, w ∈ alphabet)
    (pairs : List (I × I)) (vertices : List V) (factors : List E)
    (hvN : vertices.Nodup) (hvC : ∀ v, v ∈ vertices)
    (default : Word r Q) (n : ℕ) (fixed : List (Word r Q))
    (hsize : n + 1 + fixed.length = (headsFirstIndices vertices factors).length)
    (hhead : fixed.length < vertices.length) :
    ∃ C : ℚ, ∀ z : Word r Q,
      (sequentialHeadCount ivar factor alphabet pairs vertices factors default n (z :: fixed) : ℚ) =
        C + 2 * (alphabet.length : ℚ)^4 * (prefixOverlap z fixed : ℚ) := by
  obtain ⟨v0, hkey⟩ := headPosition_exists vertices factors hvN fixed.length hhead
  let position := fun v : V => indexCode (headsFirstIndices vertices factors) (.inl v)
  have hk : position v0 ∉ List.range' (fixed.length + 1) n := by
    change indexCode (headsFirstIndices vertices factors) (.inl v0) ∉ _
    rw [hkey]
    exact prefix_not_remaining fixed n fixed.length le_rfl
  obtain ⟨C, hC⟩ := headCount_decomposition alphabet haN haC position
    (headPosition_injective vertices factors hvC) (List.range' (fixed.length + 1) n)
    List.nodup_range' v0 hk (decode default fixed)
  refine ⟨C, ?_⟩
  intro z
  have hp : priorOverlap position (List.range' (fixed.length + 1) n)
      (position v0) (decode default fixed) z = prefixOverlap z fixed := by
    change priorOverlap position _ (indexCode (headsFirstIndices vertices factors) (.inl v0)) _ _ = _
    rw [hkey]
    exact priorHeadOverlap_eq_prefix vertices factors hvN hvC default z fixed n hsize hhead.le
  have hz := hC z
  rw [hp] at hz
  simpa only [sequentialHeadCount, List.length_cons, unweighted_head_eq ivar factor alphabet pairs
    vertices hvN hvC, decode_prefix_update, position, hkey] using hz

omit [Fintype I] [Fintype E] [DecidableEq I] in
/-- At the factor stage there is no candidate-dependent head contribution. -/
theorem sequentialHead_factor_constant
    (alphabet : List (Word r Q)) (haN : alphabet.Nodup) (haC : ∀ w, w ∈ alphabet)
    (pairs : List (I × I)) (vertices : List V) (factors : List E)
    (hvN : vertices.Nodup) (hvC : ∀ v, v ∈ vertices)
    (default : Word r Q) (n : ℕ) (fixed : List (Word r Q))
    (hfactor : vertices.length ≤ fixed.length) (x y : Word r Q) :
    sequentialHeadCount ivar factor alphabet pairs vertices factors default n (x :: fixed) =
      sequentialHeadCount ivar factor alphabet pairs vertices factors default n (y :: fixed) := by
  have ha : alphabet ≠ [] := by
    intro h
    simpa [h] using haC (fun _ => 0)
  have hk (v : V) : indexCode (headsFirstIndices vertices factors) (.inl v) ≠ fixed.length := by
    rw [headsFirst_index_head vertices factors v (hvC v)]
    have hlt : indexCode vertices v < vertices.length := List.idxOf_lt_length_iff.mpr (hvC v)
    omega
  simp only [sequentialHeadCount, List.length_cons, unweighted_head_eq ivar factor alphabet pairs
    vertices hvN hvC, decode_prefix_update]
  rw [headCount_update_outside alphabet ha (mean_word_color alphabet haN haC)
    _ _ List.nodup_range' fixed.length hk,
    headCount_update_outside alphabet ha (mean_word_color alphabet haN haC)
    _ _ List.nodup_range' fixed.length hk]

omit [Fintype I] [Fintype E] [DecidableEq I] in
theorem sequentialHead_order_iff
    (alphabet : List (Word r Q)) (haN : alphabet.Nodup) (haC : ∀ w, w ∈ alphabet)
    (pairs : List (I × I)) (vertices : List V) (factors : List E)
    (hvN : vertices.Nodup) (hvC : ∀ v, v ∈ vertices)
    (default : Word r Q) (n : ℕ) (fixed : List (Word r Q))
    (hsize : n + 1 + fixed.length = (headsFirstIndices vertices factors).length)
    (hhead : fixed.length < vertices.length) (x y : Word r Q) (A B ix iy : ℕ) :
    A * ix + B * sequentialHeadCount ivar factor alphabet pairs vertices factors default n (x :: fixed) ≤
      A * iy + B * sequentialHeadCount ivar factor alphabet pairs vertices factors default n (y :: fixed) ↔
    A * ix + (2 * alphabet.length^4 * B) * prefixOverlap x fixed ≤
      A * iy + (2 * alphabet.length^4 * B) * prefixOverlap y fixed := by
  obtain ⟨C, hC⟩ := sequentialHead_decomposition ivar factor alphabet haN haC pairs vertices factors
    hvN hvC default n fixed hsize hhead
  have h :
      (A : ℚ) * ix + B * sequentialHeadCount ivar factor alphabet pairs vertices factors default n (x :: fixed) ≤
        A * iy + B * sequentialHeadCount ivar factor alphabet pairs vertices factors default n (y :: fixed) ↔
      A * ix + (2 * (alphabet.length : ℚ)^4 * B) * prefixOverlap x fixed ≤
        A * iy + (2 * (alphabet.length : ℚ)^4 * B) * prefixOverlap y fixed := by
    rw [hC x, hC y]
    constructor <;> intro h <;> nlinarith
  exact_mod_cast h

end Sequential
end SubexponentialSAT.SqrtLog.PackingHeadIncremental

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingHeadIncrementalWeighted
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact ordering interface for the existing natural-number selector. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadIncremental

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp.LocalExpectation
open SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators

section Weighted
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ} [NeZero r]

def sequentialIncidenceCount (alphabet : List (Word r Q)) (pairs : List (I × I))
    (vertices : List V) (factors : List E) (default : Word r Q)
    (n : ℕ) (fixed : List (Word r Q)) : ℕ :=
  (PackingProgram.unweightedCounts ivar factor alphabet
    (pairs.map Sum.inl ++ headTerms (I := I) (Q := Q) vertices)
    (headsFirstIndices vertices factors) (List.range' fixed.length n)
    (decode default fixed)).1

omit [NeZero r] in
omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem sequentialNumerator_split (alphabet : List (Word r Q)) (pairs : List (I × I))
    (vertices : List V) (factors : List E) (w : PackingProgram.Weights)
    (default : Word r Q) (n : ℕ) (fixed : List (Word r Q)) :
    PackingProgram.sequentialNumerator ivar factor alphabet
      (pairs.map Sum.inl ++ headTerms (I := I) (Q := Q) vertices)
      (headsFirstIndices vertices factors) w default n fixed =
      w.incidence * sequentialIncidenceCount ivar factor alphabet pairs vertices factors default n fixed +
      w.head * sequentialHeadCount ivar factor alphabet pairs vertices factors default n fixed := by
  exact PackingProgram.numerator_split ivar factor alphabet _ _ w _ _

omit [Fintype I] [Fintype E] [DecidableEq I] in
theorem sequentialNumerator_order_head
    (alphabet : List (Word r Q)) (haN : alphabet.Nodup) (haC : ∀ z, z ∈ alphabet)
    (pairs : List (I × I)) (vertices : List V) (factors : List E)
    (hvN : vertices.Nodup) (hvC : ∀ v, v ∈ vertices)
    (w : PackingProgram.Weights) (default : Word r Q) (n : ℕ)
    (fixed : List (Word r Q))
    (hsize : n + 1 + fixed.length = (headsFirstIndices vertices factors).length)
    (hhead : fixed.length < vertices.length) (x y : Word r Q) :
    PackingProgram.sequentialNumerator ivar factor alphabet
      (pairs.map Sum.inl ++ headTerms (I := I) (Q := Q) vertices)
      (headsFirstIndices vertices factors) w default n (x :: fixed) ≤
    PackingProgram.sequentialNumerator ivar factor alphabet
      (pairs.map Sum.inl ++ headTerms (I := I) (Q := Q) vertices)
      (headsFirstIndices vertices factors) w default n (y :: fixed) ↔
      w.incidence * sequentialIncidenceCount ivar factor alphabet pairs vertices factors default n (x :: fixed) +
        (2 * alphabet.length^4 * w.head) * prefixOverlap x fixed ≤
      w.incidence * sequentialIncidenceCount ivar factor alphabet pairs vertices factors default n (y :: fixed) +
        (2 * alphabet.length^4 * w.head) * prefixOverlap y fixed := by
  rw [sequentialNumerator_split, sequentialNumerator_split]
  exact sequentialHead_order_iff ivar factor alphabet haN haC pairs vertices factors hvN hvC
    default n fixed hsize hhead x y w.incidence w.head _ _

omit [Fintype I] [Fintype E] [DecidableEq I] in
theorem sequentialNumerator_order_factor
    (alphabet : List (Word r Q)) (haN : alphabet.Nodup) (haC : ∀ z, z ∈ alphabet)
    (pairs : List (I × I)) (vertices : List V) (factors : List E)
    (hvN : vertices.Nodup) (hvC : ∀ v, v ∈ vertices)
    (w : PackingProgram.Weights) (default : Word r Q) (n : ℕ)
    (fixed : List (Word r Q)) (hfactor : vertices.length ≤ fixed.length)
    (x y : Word r Q) :
    PackingProgram.sequentialNumerator ivar factor alphabet
      (pairs.map Sum.inl ++ headTerms (I := I) (Q := Q) vertices)
      (headsFirstIndices vertices factors) w default n (x :: fixed) ≤
    PackingProgram.sequentialNumerator ivar factor alphabet
      (pairs.map Sum.inl ++ headTerms (I := I) (Q := Q) vertices)
      (headsFirstIndices vertices factors) w default n (y :: fixed) ↔
      w.incidence * sequentialIncidenceCount ivar factor alphabet pairs vertices factors default n (x :: fixed) ≤
      w.incidence * sequentialIncidenceCount ivar factor alphabet pairs vertices factors default n (y :: fixed) := by
  rw [sequentialNumerator_split, sequentialNumerator_split,
    sequentialHead_factor_constant ivar factor alphabet haN haC pairs vertices factors hvN hvC
      default n fixed hfactor x y]
  omega

end Weighted
end SubexponentialSAT.SqrtLog.PackingHeadIncremental

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingHeadIncrementalPhysical
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The exact score returned by the physical one-hot overlap loop, including
its heads-first phase gate, preserves the original selector ordering. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadIncremental
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp.LocalExpectation
open SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators

variable {r Q : ℕ}

def physicalOverlap (headCount : ℕ) (candidate : Word r Q)
    (fixed : List (Word r Q)) : ℕ :=
  if fixed.length < headCount then
    PackingHeadProgramPrefix.score (SubexponentialSAT.Subexp.ReadPlan.encodeWord candidate)
      (fixed.reverse.map SubexponentialSAT.Subexp.ReadPlan.encodeWord)
  else 0

theorem score_encode_prefix (candidate : Word r Q) (fixed : List (Word r Q)) :
    PackingHeadProgramPrefix.score (SubexponentialSAT.Subexp.ReadPlan.encodeWord candidate)
      (fixed.reverse.map SubexponentialSAT.Subexp.ReadPlan.encodeWord) =
      prefixOverlap candidate fixed := by
  simp only [PackingHeadProgramPrefix.score, List.map_map, Function.comp_def,
    PackingHeadProgramAnd.jointTrue, encodeWord_and_count]
  simp [prefixOverlap]

end SubexponentialSAT.SqrtLog.PackingHeadIncremental

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceProgramRefinement
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact conditional-incidence numerators produced by the fixed raw scorer. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp
open SubexponentialSAT.SqrtLog.Packing

section Refinement
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
  (ivar : I → V) (factor : I → E) {r Q : ℕ}

def incidenceNumerator (alphabet : List (Word r Q)) (pairs : List (I × I))
    (indices : List (V ⊕ E)) (default : Word r Q) (n : ℕ)
    (fixed : List (Word r Q)) : ℕ :=
  (PackingProgram.unweightedCounts ivar factor alphabet (pairs.map Sum.inl) indices
    (List.range' fixed.length n) (decode default fixed)).1

end Refinement
end SubexponentialSAT.SqrtLog.PackingIncidenceProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingLoaderProgramFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Framing and paid parameter serialization for the packing loader. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- A low48 native program leaves all additional metadata masters intact. -/
theorem framed_call {l n : ℕ} (p : Program 16 48 l) (outside : Store)
    {a b : State 16 48}
    (h : Trace p n (a.withPC (some p.entry)) (b.withPC none)) :
    Eval (.call (ProgramLinking.liftProgram p id lowPorts)) n
      (framed outside a) (framed outside b) := by
  have he := eval_call_lifted p id lowPorts (framed outside a)
    Function.injective_id lowPorts.injective h
  simpa only [embed_framed] using he


end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyHeads
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual head-score production from the controller table and alphabet. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

theorem headScoreRecords_eq {r Q : ℕ} (heads : ℕ) (fixed alphabet : List (Word r Q)) :
    PackingHeadProgramCandidates.scoreRecords (headRows heads fixed) (alphabet.map ReadPlan.encodeWord) =
      alphabet.map (fun candidate => UnaryCompare.encode (overlap heads fixed candidate)) := by
  simp [PackingHeadProgramCandidates.scoreRecords,PackingHeadProgramCandidates.scoreBits,
    overlap,UnaryCompare.encode,List.map_map,Function.comp_def]

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyScore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact values and uniform bounds for the two physically produced streams. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp

section Scores
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
  (ivar : I → V) (factor : I → E) {r Q : ℕ}

def candidateScore (alphabet : List (Word r Q)) (pairs : List (I × I))
    (indices : List (V ⊕ E)) (default : Word r Q) (heads s M n : ℕ)
    (fixed : List (Word r Q)) (candidate : Word r Q) : ℕ :=
  reducedScore heads s M r
    (PackingIncidenceProgram.incidenceNumerator ivar factor alphabet pairs indices default n (candidate::fixed))
    (overlap heads fixed candidate)

end Scores
end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyOrder
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Equality of all candidate comparisons with the original rational score. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp SubexponentialSAT.SqrtLog.Packing

section Ordering
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
  (ivar : I → V) (factor : I → E) {r Q : ℕ} [NeZero r]

omit [NeZero r] in
theorem overlap_eq_physical (headCount : ℕ) (fixed : List (Word r Q)) (candidate : Word r Q) :
    overlap headCount fixed candidate=PackingHeadIncremental.physicalOverlap headCount candidate fixed := by
  rw [overlap_cases]
  rfl

end Ordering
end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeKeyMapProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev Data := State 8 15

end SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

/-! Public native sparse-key mapper. The instruction table is independent of
the keys, clipping limits, coefficient width, and dictionary length. -/

end OAI.Algorithms
end


