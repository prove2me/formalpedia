-- Prove2me | Definitions.Def_OAIQ081S097
-- name    : OAIQ081S097
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:19:29.912029+00:00
-- url     : https://prove2.me/theorems/3119f135-ae19-4eb4-b291-fb50fd5f8599
-- title:
--   Definitions bundle OAIQ081S097 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 56 declarations of OpenAI's Lean: 23 definitions and 33 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadIncremental.headCount`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadIncremental.headDelta`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramPreserve.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramPreserve.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingPrefixProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.dataLength`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.CombineData`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingWeightProgram.Gate.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingWeightProgram.Gate.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingWeightProgram.Gate.cleared`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingWeightProgram.Gate.copied`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingWeightProgram.Gate.output`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingWeightProgram.Gate.ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.OuterData`, `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionGenerateProgram.inputState`, `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionGenerateProgram.outputState`, `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionGenerateProgram.sourceBudget`, `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionGenerateProgram.storedState`, `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionStreamProgram.afterClear`, `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionStreamProgram.inputState`, `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionStreamProgram.outputState`, `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionStreamProgram.sealed`, `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionStreamProgram.stageState`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_PackingHeadIncremental`, `SubexponentialSAT_SqrtLog_PackingHeadIncrementalPair`, `SubexponentialSAT_SqrtLog_PackingHeadProgramPreserve`, `SubexponentialSAT_SqrtLog_PackingPrefixProgram`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyHeads`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyScore`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyWeights`, `SubexponentialSAT_SqrtLog_PackingProgramCombine`, `SubexponentialSAT_SqrtLog_PackingWeightProgramGate`, `SubexponentialSAT_SqrtLog_PackingWeightProgramGateBasic`, `SubexponentialSAT_SqrtLog_PackingWeightProgramGateNative`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyOuter`, `SubexponentialSAT_SubexpNormalizeProgram`, `SubexponentialSAT_Subexp_ActivePlanProgram`, `SubexponentialSAT_Subexp_CollisionGenerateProgram`, `SubexponentialSAT_Subexp_CollisionStreamProgram`, `SubexponentialSAT_Subexp_CollisionTupleProgram`, `SubexponentialSAT_Subexp_PairPreparationBounds`, `SubexponentialSAT_Subexp_PairRuntimeBounds`, `SubexponentialSAT_Subexp_PairScoreProgram`, `SubexponentialSAT_Subexp_ScoreBuilderPorts`, `SubexponentialSAT_Subexp_SelectionTableProgram`, `SubexponentialSAT_Subexp_SelectorPairProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S066`, `OAIQ081S067`, `OAIQ081S069`, `OAIQ081S070`, `OAIQ081S071`, `OAIQ081S072`, `OAIQ081S073`, `OAIQ081S076`, `OAIQ081S078` and `OAIQ081S079` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S112` and `OAIQ081S113`; the proofs of `OAI.Algorithms.SubexponentialSAT.ExecPetalChildProgram.familyCall_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.TypeCompare.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.UniversalEntry.guard_eval`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixInputTypes.program_runsIn` and `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixScanStepProgram.command_eval`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S066
import Definitions.Def_OAIQ081S067
import Definitions.Def_OAIQ081S069
import Definitions.Def_OAIQ081S070
import Definitions.Def_OAIQ081S071
import Definitions.Def_OAIQ081S072
import Definitions.Def_OAIQ081S073
import Definitions.Def_OAIQ081S076
import Definitions.Def_OAIQ081S078
import Definitions.Def_OAIQ081S079

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingHeadIncrementalPair
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact uniform-completion values of one head-collision term. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadIncremental

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp.LocalExpectation
open scoped BigOperators

variable {r Q : ℕ}

theorem collision_dependsOn (t : Fin Q) (a b : ℕ) :
    DependsOn {a, b} (collision (r := r) t a b) := by
  intro ω η h
  simp only [collision, h a (by simp), h b (by simp)]

theorem collision_expectation (alphabet : List (Word r Q)) (ha : alphabet ≠ [])
    (hbalance : ∀ (t : Fin Q) (c : Fin r),
      SubexponentialSAT.ConditionalExpectation.mean alphabet
        (fun w => if w t = c then (1 : ℚ) else 0) = 1 / (r : ℚ))
    (remaining : List ℕ) (t : Fin Q) (a b : ℕ) (ω : ℕ → Word r Q) :
    wordExpectation alphabet (collision t a b) remaining ω =
      if a = b then 1 else
        if a ∈ remaining ∨ b ∈ remaining then 1 / (r : ℚ) else collision t a b ω := by
  by_cases hab : a = b
  · subst b
    have hfun : collision (r := r) t a a = fun _ => 1 := by
      funext η
      simp [collision]
    rw [hfun]
    simp only [ite_true, if_true]
    exact wordExpectation_const alphabet ha 1 remaining ω
  · simp only [ite_eq_right hab]
    induction remaining generalizing ω with
    | nil => simp [wordExpectation]
    | cons j remaining ih =>
      simp only [wordExpectation]
      simp_rw [ih]
      by_cases hr : a ∈ remaining ∨ b ∈ remaining
      · have hc : a ∈ j :: remaining ∨ b ∈ j :: remaining := by
          rcases hr with har | hbr
          · exact Or.inl (List.mem_cons_of_mem _ har)
          · exact Or.inr (List.mem_cons_of_mem _ hbr)
        simp only [ite_eq_left hr, ite_eq_left hc]
        exact SubexponentialSAT.LocalExpectation.mean_const alphabet ha _
      · obtain ⟨har, hbr⟩ := not_or.mp hr
        simp only [ite_eq_right hr]
        by_cases hja : j = a
        · subst j
          simp only [List.mem_cons, true_or, ite_true, if_true]
          simpa [collision, Function.update_of_ne (Ne.symm hab)] using hbalance t (ω b t)
        · by_cases hjb : j = b
          · subst j
            simp only [List.mem_cons, true_or, or_true, ite_true, if_true]
            simpa [collision, Function.update_of_ne hab, eq_comm] using hbalance t (ω a t)
          · have hc : ¬(a ∈ j :: remaining ∨ b ∈ j :: remaining) := by
              simp only [List.mem_cons]
              tauto
            simp only [ite_eq_right hc]
            have heq : (fun w => collision t a b (Function.update ω j w)) =
                fun _ => collision t a b ω := by
              funext w
              simp [collision, Function.update_of_ne (Ne.symm hja),
                Function.update_of_ne (Ne.symm hjb)]
            rw [heq]
            exact SubexponentialSAT.LocalExpectation.mean_const alphabet ha _

theorem pairCount_cast (alphabet : List (Word r Q)) (ha : alphabet ≠ [])
    (hbalance : ∀ (t : Fin Q) (c : Fin r),
      SubexponentialSAT.ConditionalExpectation.mean alphabet
        (fun w => if w t = c then (1 : ℚ) else 0) = 1 / (r : ℚ))
    (remaining : List ℕ) (hn : remaining.Nodup)
    (t : Fin Q) (a b : ℕ) (ω : ℕ → Word r Q) :
    (pairCount alphabet remaining t a b ω : ℚ) =
      (alphabet.length : ℚ)^4 *
        (if a = b then 1 else if a ∈ remaining ∨ b ∈ remaining then 1 / (r : ℚ)
          else collision t a b ω) := by
  have hS : (active ({a,b} : Finset ℕ) remaining).length ≤ 4 := by
    have h := active_length_le ({a,b} : Finset ℕ) remaining hn
    have hc : ({a,b} : Finset ℕ).card ≤ 2 := by
      exact (Finset.card_insert_le _ _).trans (by simp)
    omega
  have hf := wordExpectation_filter alphabet ha ({a,b} : Finset ℕ)
    (collision (r := r) t a b) (collision_dependsOn t a b) remaining ω
  have hs := local_average_eq_scaledCount alphabet ha
    (fun η : ℕ → Word r Q => if η a t = η b t then 1 else 0)
    ({a,b} : Finset ℕ) 4 remaining hS ω
  have hdiv : wordExpectation alphabet (collision t a b) remaining ω =
      (pairCount alphabet remaining t a b ω : ℚ) / (alphabet.length : ℚ)^4 := by
    rw [hf]
    change wordExpectation alphabet (fun η => if η a t = η b t then 1 else 0)
      (active {a, b} remaining) ω = _
    simpa only [pairCount, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using hs
  rw [collision_expectation alphabet ha hbalance] at hdiv
  have hq : (alphabet.length : ℚ) ≠ 0 := by
    exact_mod_cast (List.length_pos_iff.mpr ha).ne'
  have hmul := (eq_div_iff (pow_ne_zero 4 hq)).mp hdiv
  simpa only [mul_comm] using hmul.symm

end SubexponentialSAT.SqrtLog.PackingHeadIncremental

end OAI.Algorithms
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

def headCount {V : Type*} [Fintype V] (alphabet : List (Word r Q))
    (position : V → ℕ) (remaining : List ℕ) (ω : ℕ → Word r Q) : ℕ :=
  ∑ t : Fin Q, ∑ v : V, ∑ u : V,
    pairCount alphabet remaining t (position v) (position u) ω

def headDelta (remaining : List ℕ) (key : ℕ) (ω : ℕ → Word r Q)
    (z : Word r Q) (t : Fin Q) (a : ℕ) : ℚ :=
  if a = key ∨ a ∈ remaining then 0 else
    (if z t = ω a t then 1 else 0) - collision t key a ω

theorem pairCount_update (alphabet : List (Word r Q)) (ha : alphabet ≠ [])
    (hbalance : ∀ (t : Fin Q) (c : Fin r),
      SubexponentialSAT.ConditionalExpectation.mean alphabet
        (fun w => if w t = c then (1 : ℚ) else 0) = 1 / (r : ℚ))
    (remaining : List ℕ) (hn : remaining.Nodup) (key : ℕ) (hk : key ∉ remaining)
    (t : Fin Q) (a b : ℕ) (ω : ℕ → Word r Q) (z : Word r Q) :
    (pairCount alphabet remaining t a b (Function.update ω key z) : ℚ) =
      (pairCount alphabet remaining t a b ω : ℚ) + (alphabet.length : ℚ)^4 *
        ((if a = key then headDelta remaining key ω z t b else 0) +
         (if b = key then headDelta remaining key ω z t a else 0)) := by
  rw [pairCount_cast alphabet ha hbalance remaining hn,
    pairCount_cast alphabet ha hbalance remaining hn]
  by_cases hak : a = key <;> by_cases hbk : b = key <;>
    by_cases hab : a = b <;> by_cases har : a ∈ remaining <;>
    by_cases hbr : b ∈ remaining <;>
    simp_all [collision, headDelta, eq_comm] <;> split_ifs <;> ring

theorem sum_headDelta {V : Type*} [Fintype V] (position : V → ℕ)
    (remaining : List ℕ) (key : ℕ) (ω : ℕ → Word r Q) (z : Word r Q) :
    (∑ t : Fin Q, ∑ v : V, headDelta remaining key ω z t (position v)) =
      (priorOverlap position remaining key ω z : ℚ) -
        (priorOverlap position remaining key ω (ω key) : ℚ) := by
  simp only [priorOverlap, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Nat.cast_one,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro v hv
  by_cases h : position v = key ∨ position v ∈ remaining
  · simp [headDelta, h]
  · simp [headDelta, collision, h]

/-- Both ordered orientations contribute. The self term and all terms with
unassigned partners are candidate-independent. -/
theorem headCount_update {V : Type*} [Fintype V] [DecidableEq V]
    (alphabet : List (Word r Q)) (ha : alphabet ≠ [])
    (hbalance : ∀ (t : Fin Q) (c : Fin r),
      SubexponentialSAT.ConditionalExpectation.mean alphabet
        (fun w => if w t = c then (1 : ℚ) else 0) = 1 / (r : ℚ))
    (position : V → ℕ) (hinj : Function.Injective position)
    (remaining : List ℕ) (hn : remaining.Nodup) (v0 : V)
    (hk : position v0 ∉ remaining) (ω : ℕ → Word r Q) (z : Word r Q) :
    (headCount alphabet position remaining (Function.update ω (position v0) z) : ℚ) =
      (headCount alphabet position remaining ω : ℚ) + 2 * (alphabet.length : ℚ)^4 *
        ((priorOverlap position remaining (position v0) ω z : ℚ) -
         (priorOverlap position remaining (position v0) ω (ω (position v0)) : ℚ)) := by
  simp only [headCount, Nat.cast_sum]
  simp_rw [pairCount_update alphabet ha hbalance remaining hn (position v0) hk,
    hinj.eq_iff]
  simp only [ Finset.sum_add_distrib, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true,
    ← Finset.mul_sum]
  rw [← sum_headDelta position remaining (position v0) ω z]
  ring

/-- The complete head contribution differs from the incremental overlap by
one common rational constant. The physical comparison never computes it. -/
theorem headCount_decomposition {V : Type*} [Fintype V] [DecidableEq V] [NeZero r]
    (alphabet : List (Word r Q)) (haN : alphabet.Nodup)
    (haC : ∀ w, w ∈ alphabet)
    (position : V → ℕ) (hinj : Function.Injective position)
    (remaining : List ℕ) (hn : remaining.Nodup) (v0 : V)
    (hk : position v0 ∉ remaining) (ω : ℕ → Word r Q) :
    ∃ C : ℚ, ∀ z : Word r Q,
      (headCount alphabet position remaining (Function.update ω (position v0) z) : ℚ) =
        C + 2 * (alphabet.length : ℚ)^4 *
          (priorOverlap position remaining (position v0) ω z : ℚ) := by
  have ha : alphabet ≠ [] := by
    intro h
    simpa [h] using haC (fun _ => 0)
  refine ⟨(headCount alphabet position remaining ω : ℚ) -
    2 * (alphabet.length : ℚ)^4 *
      (priorOverlap position remaining (position v0) ω (ω (position v0)) : ℚ), ?_⟩
  intro z
  rw [headCount_update alphabet ha (Packing.mean_word_color alphabet haN haC)
    position hinj remaining hn v0 hk ω z]
  ring

theorem headCount_update_outside {V : Type*} [Fintype V]
    (alphabet : List (Word r Q)) (ha : alphabet ≠ [])
    (hbalance : ∀ (t : Fin Q) (c : Fin r),
      SubexponentialSAT.ConditionalExpectation.mean alphabet
        (fun w => if w t = c then (1 : ℚ) else 0) = 1 / (r : ℚ))
    (position : V → ℕ) (remaining : List ℕ) (hn : remaining.Nodup)
    (key : ℕ) (hk : ∀ v, position v ≠ key) (ω : ℕ → Word r Q) (z : Word r Q) :
    headCount alphabet position remaining (Function.update ω key z) =
      headCount alphabet position remaining ω := by
  have h : (headCount alphabet position remaining (Function.update ω key z) : ℚ) =
      (headCount alphabet position remaining ω : ℚ) := by
    simp only [headCount, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro t ht
    apply Finset.sum_congr rfl
    intro v hv
    apply Finset.sum_congr rfl
    intro u hu
    rw [pairCount_cast alphabet ha hbalance remaining hn,
      pairCount_cast alphabet ha hbalance remaining hn]
    simp only [collision, Function.update_of_ne (hk v), Function.update_of_ne (hk u)]
  exact_mod_cast h

end SubexponentialSAT.SqrtLog.PackingHeadIncremental

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingHeadProgramPreserve
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A source-preserving wrapper for the actual prefix scan. The only input
streams are one candidate, the flattened prior words, and their unary count. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadProgramPreserve
open SubexponentialSAT BitProgram StructuredCalls StackRoutines SubexpScanPrimitives
open scoped BigOperators

abbrev Data := State 5 8

def state (candidate table : List Bool) (n : ℕ) (out : List Bool)
    (tableCopy countCopy : List Bool := []) : Data :=
  ⟨fun _ => false, ![candidate,table,[],[],out,List.replicate n true,tableCopy,countCopy]⟩

theorem copyTable_eval (candidate table : List Bool) (n : ℕ) (out : List Bool) :
    Eval copyTable (7*table.length+5) (state candidate table n out)
      (state candidate table n out table []) := by
  have h := copy_eval (state candidate table n out) 1 6 2 0 1
    (by decide) (by decide) (by decide) (by decide) (by simp [state])
  have hz : afterCopy (state candidate table n out) 1 6 0 1 = state candidate table n out table [] := by
    apply state_ext <;> funext i <;> fin_cases i <;> simp [state,afterCopy,copyStacks,readRegs]
  rw [hz] at h
  simpa [copyTable,state] using h

theorem copyCount_eval (candidate table : List Bool) (n : ℕ) (out : List Bool) :
    Eval copyCount (7*n+5) (state candidate table n out table [])
      (state candidate table n out table (List.replicate n true)) := by
  have h := copy_eval (state candidate table n out table []) 5 7 2 0 1
    (by decide) (by decide) (by decide) (by decide) (by simp [state])
  have hz : afterCopy (state candidate table n out table []) 5 7 0 1 =
      state candidate table n out table (List.replicate n true) := by
    apply state_ext <;> funext i <;> fin_cases i <;> simp [state,afterCopy,copyStacks,readRegs]
  rw [hz] at h
  simpa [copyCount,state] using h

end SubexponentialSAT.SqrtLog.PackingHeadProgramPreserve

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

/-- A correctness interface for normalization's actual filter callback. The
conclusion tracks `reverse (List.filter keep records)` exactly. Applying
`reverseRecordsProgram` afterward restores `List.filter` order. -/
theorem filter_iterate_run {r s : ℕ} (ports : RecordPrograms.Ports r s)
    (callback : StructuredCalls.Cmd r s) (keep : List Bool → Bool)
    (cost : List Bool → ℕ) (invariant : StructuredProgram.State r s → Prop)
    (output : Fin s)
    (hsource : output ≠ ports.source) (hpayload : output ≠ ports.payload)
    (contract : RecordPrograms.CallbackContractWith ports callback
      (fun _ => false) cost invariant (FilterEffect output keep))
    (records acc : List (List Bool)) (suffix : List Bool)
    (base : StructuredProgram.State r s) (hbase : invariant base)
    (hacc : base.stacks output = Encoding.encodeList id acc) (v p f : Bool) :
    ∃ (n : ℕ) (next : StructuredProgram.State r s),
      n ≤ 3 + RecordPrograms.budget cost records ∧ invariant next ∧
      (RecordPrograms.state ports next false true false suffix []).stacks output =
        Encoding.encodeList id ((records.filter keep).reverse ++ acc) ∧
      StructuredCalls.Eval (RecordPrograms.iterate ports callback) n
        (RecordPrograms.state ports base v p f (Encoding.encodeList id records ++ suffix) [])
        (RecordPrograms.state ports next false true false suffix []) := by
  obtain ⟨n, next, hn, hnext, hhistory, hrun⟩ :=
    RecordPrograms.iterate_run_with ports callback (fun _ => false) cost invariant
      (FilterEffect output keep) contract records suffix base hbase v p f
  have hout := filterVisits_result output keep hhistory acc hacc
  have hany : records.any (fun _ => false) = false := by
    induction records <;> simp_all
  have hfinal := (RecordPrograms.state_stack_frame ports next false true false
    suffix [] output hsource hpayload).trans hout
  exact ⟨n, next, hn, hnext, hfinal, by simpa [hany] using hrun⟩

end SubexponentialSAT.SubexpNormalizeProgram

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

abbrev Data := State 3 11

end SubexponentialSAT.SqrtLog.PackingPrefixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CollisionStreamProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

/-- The actual equality trace, including preserved external stacks and bounds
on the suffixes which the cleanup stage must consume. -/
theorem equality_eval (d : Data) :
    ∃ n ≤ 9 * ((d.stacks 1).length + 1), ∃ e : Data,
      Eval (.call equalityProgram) n d e ∧
      e.regs 4 = decide (d.stacks 1 = d.stacks 12) ∧
      (e.stacks 1).length ≤ (d.stacks 1).length ∧
      (e.stacks 12).length ≤ (d.stacks 12).length ∧
      (∀ j, j ≠ 1 → j ≠ 12 → e.stacks j = d.stacks j) := by
  obtain ⟨c, ⟨n, hn, ht⟩, hp, hout, hleft, hright⟩ :=
    ExecClauseCost.bitEquality_runsIn_bounded d.regs (d.stacks 1) (d.stacks 12)
  let a : StructuredProgram.State 5 2 :=
    ⟨d.regs, ExecClauseCost.bitStacks (d.stacks 1) (d.stacks 12)⟩
  let b : StructuredProgram.State 5 2 := ⟨c.regs, c.stacks⟩
  let e := embedState id equalityPorts d b
  have ha : embedState id equalityPorts d a = d := by
    apply embedState_eq _ _ Function.injective_id equalityPorts_injective
    · intro j; rfl
    · intro j; fin_cases j <;> simp [a, equalityPorts, ExecClauseCost.bitStacks]
    · intros; rfl
    · intros; rfl
  have hcfg : b.withPC none = c := by
    cases c
    simp_all [b, StructuredProgram.State.withPC]
  have ht' : Trace ExecClauseCost.bitEqualityProgram n
      (a.withPC (some ExecClauseCost.bitEqualityProgram.entry)) (b.withPC none) := by
    rw [hcfg]
    exact ht
  have he := eval_call_lifted ExecClauseCost.bitEqualityProgram id equalityPorts d
    Function.injective_id equalityPorts_injective ht'
  refine ⟨n, hn, e, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [ha, equalityProgram] using he
  · change (embedState id equalityPorts d b).regs (id 4) = _
    rw [embedState_register _ _ _ _ Function.injective_id]
    exact hout
  · change ((embedState id equalityPorts d b).stacks (equalityPorts 0)).length ≤ _
    rw [embedState_stack _ _ _ _ equalityPorts_injective]
    exact hleft
  · change ((embedState id equalityPorts d b).stacks (equalityPorts 1)).length ≤ _
    rw [embedState_stack _ _ _ _ equalityPorts_injective]
    exact hright
  · intro j hj1 hj12
    exact embedState_stack_frame _ _ _ _ j (by
      rintro ⟨i, hi⟩
      fin_cases i <;> simp_all [equalityPorts])

def afterClear (d : Data) (src : Fin 13) : Data :=
  ⟨readRegs d.regs 0 1 none, clearStacks src d.stacks⟩

theorem clear_eval (d : Data) (src : Fin 13) :
    Eval (.call (clearProgram src (0 : Fin 5) 1))
      (2 * (d.stacks src).length + 3) d (afterClear d src) := by
  apply Eval.call
  have h := halt_after_trace _ (clearProgram_trace src (0 : Fin 5) 1 d.regs d.stacks)
    2 rfl rfl
  simpa [afterClear, StructuredProgram.State.withPC, clearResult, clearProgram,
    Nat.add_assoc] using h

def sealed (d : Data) (answer : Bool) : Data :=
  ⟨fun _ => false,
    Function.update (Function.update (Function.update d.stacks 1 []) 12 [])
      11 (answer :: d.stacks 11)⟩

theorem finish_eval (d : Data) :
    Eval finishCommand (2 * (d.stacks 1).length + 2 * (d.stacks 12).length + 10)
      d (sealed d (d.regs 4)) := by
  let d1 := afterClear d 1
  let d2 := afterClear d1 12
  let d3 := (StructuredProgram.Atom.push (11 : Fin 13) (4 : Fin 5)).eval d2
  let d4 := (StructuredProgram.Atom.set (2 : Fin 5) false).eval d3
  let d5 := (StructuredProgram.Atom.set (3 : Fin 5) false).eval d4
  let d6 := (StructuredProgram.Atom.set (4 : Fin 5) false).eval d5
  have hf : d6 = sealed d (d.regs 4) := by
    apply state_ext
    · funext j
      fin_cases j <;> simp [d6, d5, d4, d3, d2, d1, afterClear, sealed, readRegs,
        StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr]
    · funext j
      simp [d6, d5, d4, d3, d2, d1, afterClear, sealed, readRegs, clearStacks,
        StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr]
  have he : Eval finishCommand
      ((2 * (d.stacks 1).length + 3) +
        ((2 * (d1.stacks 12).length + 3) + (1 + (1 + (1 + 1))))) d d6 :=
    .seq (clear_eval d 1) (.seq (clear_eval d1 12)
      (.seq (.base (.atom _ _)) (.seq (.base (.atom _ _))
        (.seq (.base (.atom _ _)) (.base (.atom _ _))))))
  rw [hf] at he
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  simp [d1, afterClear, clearStacks]
  omega

/-- Comparing, cleaning, and emitting is a fixed-code operation. Every stack
outside the two type buffers and the stream is preserved. -/
theorem seal_eval (d : Data) :
    ∃ n ≤ 11 * (d.stacks 1).length + 2 * (d.stacks 12).length + 19,
      Eval sealCommand n d (sealed d (decide (d.stacks 1 = d.stacks 12))) := by
  obtain ⟨n, hn, e, he, hout, hl, hr, hframe⟩ := equality_eval d
  have hf := finish_eval e
  have hseal : sealed e (e.regs 4) = sealed d (decide (d.stacks 1 = d.stacks 12)) := by
    apply state_ext
    · rfl
    · funext j
      by_cases h1 : j = 1
      · subst j; simp [sealed]
      by_cases h12 : j = 12
      · subst j; simp [sealed]
      by_cases h11 : j = 11
      · subst j; simp [sealed, hout, hframe 11 (by decide) (by decide)]
      · simp [sealed, h1, h12, h11, hframe j h1 h12]
  rw [hseal] at hf
  exact ⟨n + (2 * (e.stacks 1).length + 2 * (e.stacks 12).length + 10),
    by omega, he.seq hf⟩

/-- State at a callback boundary. The two plan arguments are serialized bytes;
after a gather its plan is consumed. Only the row table, width, and stream are
persistent at this boundary. -/
def stageState (rows : List (List Bool)) (width left right planLeft planRight stream : List Bool) :
    Data :=
  ⟨fun _ => false,
    fun j => if j = 0 then rows.flatten else if j = 3 then width
      else if j = 1 then left else if j = 12 then right
      else if j = 8 then planLeft else if j = 10 then planRight
      else if j = 11 then stream else []⟩

def inputState (rows : List (List Bool)) (width : List Bool)
    (left right : List ℕ) (stream : List Bool) : Data :=
  stageState rows width [] [] (planBytes left) (planBytes right) stream

def outputState (rows : List (List Bool)) (width stream : List Bool) : Data :=
  stageState rows width [] [] [] [] stream

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

theorem embed_state (f : Frame) (table workLeft workRight stream : List Bool)
    (rows : List (List Bool)) (htable : rows.flatten = table) :
    embedState lowRegs lowStacks (state f table workLeft workRight stream [])
      (CollisionStreamProgram.stageState rows f.width [] [] workLeft workRight stream) =
        state f table workLeft workRight stream [] := by
  apply state_ext
  · funext j
    by_cases hj : j.val < 5
    · let i : Fin 5 := ⟨j.val, hj⟩
      have hi : lowRegs i = j := Fin.ext rfl
      rw [← hi, embedState_register _ _ _ _ lowRegs_injective]
      clear_value i
      fin_cases i <;> simp [lowRegs, state, CollisionStreamProgram.stageState]
    · rw [embedState_register_frame _ _ _ _ j (by
        rintro ⟨i, hi⟩; apply hj
        have he := congrArg Fin.val hi; exact he ▸ i.isLt)]
  · funext j
    by_cases hj : j.val < 13
    · let i : Fin 13 := ⟨j.val, hj⟩
      have hi : lowStacks i = j := Fin.ext rfl
      rw [← hi, embedState_stack _ _ _ _ lowStacks_injective]
      clear_value i
      fin_cases i <;> simp [lowStacks, state, CollisionStreamProgram.stageState, htable]
    · rw [embedState_stack_frame _ _ _ _ j (by
        rintro ⟨i, hi⟩; apply hj
        have he := congrArg Fin.val hi; exact he ▸ i.isLt)]

theorem embed_output (f : Frame) (rows : List (List Bool)) (stream answer : List Bool) :
    embedState lowRegs lowStacks
      (state f rows.flatten (CollisionStreamProgram.planBytes f.left)
        (CollisionStreamProgram.planBytes f.right) stream [])
      (CollisionStreamProgram.outputState rows f.width answer) =
        state f rows.flatten [] [] answer [] := by
  apply state_ext
  · funext j
    by_cases hj : j.val < 5
    · let i : Fin 5 := ⟨j.val, hj⟩
      have hi : lowRegs i = j := Fin.ext rfl
      rw [← hi, embedState_register _ _ _ _ lowRegs_injective]
      clear_value i
      fin_cases i <;> simp [lowRegs, state, CollisionStreamProgram.outputState,
        CollisionStreamProgram.stageState]
    · rw [embedState_register_frame _ _ _ _ j (by
        rintro ⟨i, hi⟩; apply hj
        have he := congrArg Fin.val hi; exact he ▸ i.isLt)]
      rfl
  · funext j
    by_cases hj : j.val < 13
    · let i : Fin 13 := ⟨j.val, hj⟩
      have hi : lowStacks i = j := Fin.ext rfl
      rw [← hi, embedState_stack _ _ _ _ lowStacks_injective]
      clear_value i
      fin_cases i <;> simp [lowStacks, state, CollisionStreamProgram.outputState,
        CollisionStreamProgram.stageState]
    · rw [embedState_stack_frame _ _ _ _ j (by
        rintro ⟨i, hi⟩; apply hj
        have he := congrArg Fin.val hi; exact he ▸ i.isLt)]
      have h0 : j ≠ 0 := by intro h; subst j; exact hj (by decide)
      have h3 : j ≠ 3 := by intro h; subst j; exact hj (by decide)
      have h8 : j ≠ 8 := by intro h; subst j; exact hj (by decide)
      have h10 : j ≠ 10 := by intro h; subst j; exact hj (by decide)
      have h11 : j ≠ 11 := by intro h; subst j; exact hj (by decide)
      simp [state, h0, h3, h8, h10, h11]

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

def storedState (regs : Fin 10 → Bool) (current width : List Bool) (left right : List ℕ)
    (alphabet depth tuples work stream : List Bool) : Data :=
  ⟨regs, fun j => if j = 3 then width else if j = 13 then current
    else if j = 14 then CollisionStreamProgram.planBytes left
    else if j = 15 then CollisionStreamProgram.planBytes right
    else if j = 19 then alphabet else if j = 17 then depth else if j = 16 then tuples
    else if j = 6 then work else if j = 11 then stream else []⟩

def inputState (current width : List Bool) (left right : List ℕ)
    (alphabet : List (List Bool)) (depth stream : List Bool) : Data :=
  storedState (fun _ => false) current width left right
    (ProgramEncoding.encodeRecords alphabet) depth [] [] stream

theorem resetList_eval (indices : List (Fin 10)) (d : Data) :
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

theorem reset_eval (d : Data) :
    Eval resetCommand 10 d ⟨fun _ => false, d.stacks⟩ := by
  have he := resetList_eval (List.finRange 10) d
  have hr : resetValues (List.finRange 10) d.regs = fun _ => false := by
    funext i
    simp [resetValues_apply]
  rw [hr] at he
  simpa [resetCommand] using Eval.base he

theorem clearWork_eval (regs : Fin 10 → Bool) (current width : List Bool) (left right : List ℕ)
    (alphabet tuples stream : List Bool) :
    Eval clearWork 5
      (storedState regs current width left right alphabet [] tuples [false] stream)
      (storedState (readRegs regs 0 1 none) current width left right alphabet [] tuples [] stream) := by
  let d := storedState regs current width left right alphabet [] tuples [false] stream
  have h := halt_after_trace _ (clearProgram_trace (6 : Fin 20) (0 : Fin 10) 1 d.regs d.stacks)
    2 rfl rfl
  have hs : clearStacks (6 : Fin 20) d.stacks =
      (storedState (readRegs regs 0 1 none) current width left right alphabet [] tuples [] stream).stacks := by
    funext j
    by_cases h6 : j = 6
    · subst j; simp [d, storedState, clearStacks]
    · simp [d, storedState, clearStacks, h6]
  simp only [clearResult] at h
  rw [hs] at h
  apply Eval.call
  simpa [d, clearWork, clearProgram, storedState,
    StructuredProgram.State.withPC] using h

def outputState (current width : List Bool) (left right : List ℕ)
    (alphabet stream : List Bool) : Data :=
  storedState (fun j => decide (j = 6)) current width left right alphabet [] [] [] stream

def sourceBudget (current : List Bool) (width : ℕ) (left right : List ℕ)
    (alphabet : List (List Bool)) (depth : ℕ) : ℕ :=
  TupleProgram.powerCost alphabet depth [[]] +
    CollisionTupleProgram.sourceBudget current width left right
      (TupleProgram.powerRows alphabet depth [[]]) + 25

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

theorem clear_eval (src : Fin 26) (d : Data) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d (cleared src d) := by
  apply Eval.call
  simpa [clear, cleared, clearProgram, clearResult,
    StructuredProgram.State.withPC, Nat.add_assoc] using
    halt_after_trace _ (clearProgram_trace src (0 : Fin 13) 1 d.regs d.stacks) 2 rfl rfl

end SubexponentialSAT.Subexp.PairScoreProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingWeightProgramGateBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingWeightProgram.Gate
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 4 7
def copied (d : Data) (src dst : Fin 7) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks src dst d.stacks⟩
def cleared (d : Data) (j : Fin 7) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks j []⟩

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

def ready (d : Data) : Prop := ∀ j : Fin 7, 2 ≤ j.val → d.stacks j = []
def output (d : Data) : List Bool :=
  if (d.stacks 1).length < CounterPrograms.value (d.stacks 0) then d.stacks 1 else []
def budget (d : Data) : ℕ := CounterConversions.runtimeBound (d.stacks 0) +
  7 * (d.stacks 0).length + 20 * (d.stacks 1).length +
  2 * CounterPrograms.value (d.stacks 0) + 30

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

/-- The unary expansion is paid in the numeric value n, not only its bit size. -/
theorem budget_le (d : Data) : budget d ≤
    80 * (CounterPrograms.value (d.stacks 0) + (d.stacks 1).length + (d.stacks 0).length + 1)^2 := by
  unfold budget CounterConversions.runtimeBound
  nlinarith [Nat.zero_le (CounterPrograms.value (d.stacks 0) * (d.stacks 1).length),
    Nat.zero_le ((d.stacks 0).length * (d.stacks 1).length)]

end SubexponentialSAT.SqrtLog.PackingWeightProgram.Gate

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

theorem headRows_flatten_length {r Q : ℕ} (heads : ℕ) (fixed : List (Word r Q)) :
    (headRows heads fixed).flatten.length=headCount heads fixed*ReadPlan.wordWidth r Q := by
  unfold headRows headCount
  split
  · simpa using encodedWords_length fixed.reverse
  · simp

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

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

theorem plan_sizes_le_bytes (plan : List ℕ) :
    plan.sum ≤ (CollisionStreamProgram.planBytes plan).length ∧
      plan.length ≤ (CollisionStreamProgram.planBytes plan).length := by
  have h := GatherProgram.encoded_plan_length plan
  change (CollisionStreamProgram.planBytes plan).length = _ at h
  omega

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

theorem embed_emit (regs : Regs) (v p f : Bool)
    (source plan threshold acc query output source' threshold' acc' query' : List Bool) :
    embedState emitRegs emitStack (state regs source plan threshold acc query output)
      (SubexpNormalizeProgram.filterState v p f source' threshold' acc' query') =
      state (flags regs v p f) source' plan threshold' acc' query' output := by
  apply embedState_eq_of_ports _ _ _ _ _ emitRegs_injective emitStack_injective
  · intro i; fin_cases i <;> simp [ flags, emitRegs, SubexpNormalizeProgram.filterState,
      SubexpPostfixControl.triple]
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
    have h1 : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
    have h9 : i ≠ 9 := fun h => hi ⟨2, h.symm⟩
    simp [ flags, h0, h1, h9]
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h5 : i ≠ 5 := fun h => hi ⟨0, h.symm⟩
    have h7 : i ≠ 7 := fun h => hi ⟨1, h.symm⟩
    have h8 : i ≠ 8 := fun h => hi ⟨2, h.symm⟩
    have h2 : i ≠ 2 := fun h => hi ⟨3, h.symm⟩
    fin_cases i <;> simp_all []

theorem embed_reverse (regs : Regs) (v p f : Bool)
    (source plan threshold acc query output src' threshold' out' query' : List Bool) :
    embedState emitRegs reverseStack (state regs source plan threshold acc query output)
      (SubexpNormalizeProgram.filterState v p f src' threshold' out' query') =
      state (flags regs v p f) source plan threshold' src' query' out' := by
  apply embedState_eq_of_ports _ _ _ _ _ emitRegs_injective reverseStack_injective
  · intro i; fin_cases i <;> simp [ flags, emitRegs, SubexpNormalizeProgram.filterState,
      SubexpPostfixControl.triple]
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
    have h1 : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
    have h9 : i ≠ 9 := fun h => hi ⟨2, h.symm⟩
    simp [ flags, h0, h1, h9]
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h8 : i ≠ 8 := fun h => hi ⟨0, h.symm⟩
    have h7 : i ≠ 7 := fun h => hi ⟨1, h.symm⟩
    have h11 : i ≠ 11 := fun h => hi ⟨2, h.symm⟩
    have h2 : i ≠ 2 := fun h => hi ⟨3, h.symm⟩
    fin_cases i <;> simp_all []

end SubexponentialSAT.Subexp.ActivePlanProgram

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

theorem emitter_eval (bits source counter acc : List Bool) (v p f : Bool) :
    Eval (.call emitter) (5 * bits.length + 7)
      (state v p f source bits.reverse counter [] acc [])
      (state true false f source [] counter (true :: Encoding.frame bits) acc []) := by
  let a := SubexpNormalizeProgram.filterState v p f source counter [] bits.reverse
  let b := SubexpNormalizeProgram.filterState true false f source counter
    (true :: Encoding.frame bits) []
  let base := state v p f source bits.reverse counter [] acc []
  have ha : embedState id emitStack base a = base := by
    apply embed_eq _ _ Function.injective_id emitStack_injective
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> rfl
    · intro j hj; exact False.elim (hj ⟨j, rfl⟩)
    · intro j hj; rfl
  have hb : embedState id emitStack base b =
      state true false f source [] counter (true :: Encoding.frame bits) acc [] := by
    apply embed_eq _ _ Function.injective_id emitStack_injective
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> rfl
    · intro j hj; exact False.elim (hj ⟨j, rfl⟩)
    · intro j hj
      have h1 : j ≠ 1 := fun h => hj ⟨3, by simpa [emitStack] using h.symm⟩
      have h3 : j ≠ 3 := fun h => hj ⟨2, by simpa [emitStack] using h.symm⟩
      fin_cases j <;> simp_all [emitStack, state, base]
  have ht : Trace SubexpNormalizeProgram.emitRecordProgram (5 * bits.length + 7)
      (a.withPC (some SubexpNormalizeProgram.emitRecordProgram.entry)) (b.withPC none) := by
    simpa [a, b] using SubexpNormalizeProgram.emitRecord_trace bits source counter [] v p f
  have h := eval_call_lifted SubexpNormalizeProgram.emitRecordProgram id emitStack base
    Function.injective_id emitStack_injective (a := a) (b := b) ht
  simpa only [ha, hb, emitter] using h

theorem emitToAcc_eval (bits source counter acc : List Bool) (v p f : Bool) :
    Eval emitToAcc (11 * bits.length + 14)
      (state v p f source bits.reverse counter [] acc [])
      (state false false f source [] counter [] ((Encoding.frame bits).reverse ++ acc) []) := by
  have h₁ := emitter_eval bits source counter acc v p f
  have h₂ := pop_tag_eval bits source counter acc f
  have h₃ := transfer_eval (3 : Fin 6) 4 (by decide)
    (state true true f source [] counter (Encoding.frame bits) acc []).regs
    (state true true f source [] counter (Encoding.frame bits) acc []).stacks
  have hout : (⟨readRegs (state true true f source [] counter (Encoding.frame bits) acc []).regs 0 1 none,
      transferStacks 3 4 (state true true f source [] counter (Encoding.frame bits) acc []).stacks⟩ : Data) =
      state false false f source [] counter [] ((Encoding.frame bits).reverse ++ acc) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
    · funext i; fin_cases i <;> simp [state, transferStacks]
  rw [hout] at h₃
  have ht := Eval.seq h₁ (Eval.seq h₂ h₃)
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  all_goals simp [ state, Encoding.length_frame]
  all_goals omega

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

theorem prepareRight_eval (regs : Fin 8 → Bool) (table left right acc : List Bool) :
    ∃ regs', Eval prepareRight (3 * left.length + 9 * right.length + 11)
      (state regs [] table left right [] acc)
      (state regs' right table [] [] left.reverse acc) := by
  let a := state regs [] table left right [] acc
  let b : Data := ⟨readRegs a.regs 0 1 none, StackRoutines.transferStacks 8 10 a.stacks⟩
  let c : Data := ⟨readRegs b.regs 0 1 none, StackRoutines.copyStacks 9 6 b.stacks⟩
  let d : Data := ⟨readRegs c.regs 0 1 none, StackRoutines.clearStacks 9 c.stacks⟩
  have h1 := TupleProgram.transfer_eval (8 : Fin 12) 10 (0 : Fin 8) 1
    (by decide) (by decide) a
  have h2 := TupleProgram.copy_eval (9 : Fin 12) 6 4 (0 : Fin 8) 1
    (by decide) (by decide) (by decide) (by decide) b (by rfl)
  have h3 := TupleProgram.clear_eval (9 : Fin 12) (0 : Fin 8) 1 c
  have hd : d = state d.regs right table [] [] left.reverse acc := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      fin_cases j <;>
        simp [ c, b, a, state, StackRoutines.transferStacks,
          StackRoutines.copyStacks, StackRoutines.clearStacks]
  refine ⟨d.regs, ?_⟩
  rw [← hd]
  convert h1.seq (h2.seq h3) using 1 ;
    simp [ a, b, c, state, StackRoutines.transferStacks,
      StackRoutines.copyStacks] ; omega

end SubexponentialSAT.Subexp.SelectorPairProgram

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

theorem planBytes_length (plan : List ℕ) :
    (CollisionStreamProgram.planBytes plan).length = 2 * plan.sum + 2 * plan.length + 1 :=
  GatherProgram.encoded_plan_length plan

theorem plan_sizes_le (plan : List ℕ) :
    plan.sum ≤ (CollisionStreamProgram.planBytes plan).length ∧
      plan.length ≤ (CollisionStreamProgram.planBytes plan).length := by
  rw [planBytes_length]
  omega

end SubexponentialSAT.Subexp.PairPreparationBounds

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

/-- Two transfers restore the original byte order of the score records. The
selected-pair table is then cleared by actual pop instructions. -/
theorem finish_eval (d : Data) (hzero : d.stacks 0 = []) (htmp : d.stacks 42 = []) :
    Eval finish (6 * (d.stacks 41).length + 2 * (d.stacks 40).length + 9) d (finished d) := by
  let a : Data := ⟨readRegs d.regs 0 1 none, transferStacks 41 42 d.stacks⟩
  let b : Data := ⟨readRegs a.regs 0 1 none, transferStacks 42 0 a.stacks⟩
  have h₁ := TupleProgram.transfer_eval (41 : Fin 48) 42 (0 : Fin 16) 1
    (by decide) (by decide) d
  have h₂ := TupleProgram.transfer_eval (42 : Fin 48) 0 (0 : Fin 16) 1
    (by decide) (by decide) a
  have h₃ := TupleProgram.clear_eval (40 : Fin 48) (0 : Fin 16) 1 b
  have he : (⟨readRegs b.regs 0 1 none, clearStacks 40 b.stacks⟩ : Data) = finished d := by
    apply congrArg₂ StructuredProgram.State.mk
    · simp [a, b, readRegs_reset]
    · funext j
      by_cases h0 : j = 0
      · subst j; simp [a, b, clearStacks, transferStacks, hzero, htmp]
      by_cases h40 : j = 40
      · subst j; simp [a, b, clearStacks, transferStacks, hzero, htmp]
      by_cases h41 : j = 41
      · subst j; simp [a, b, clearStacks, transferStacks, hzero, htmp]
      by_cases h42 : j = 42
      · subst j; simp [a, b, clearStacks, transferStacks, hzero, htmp]
      · simp [a, b, clearStacks, transferStacks, hzero, htmp, h0, h40, h41, h42]
  rw [he] at h₃
  have h := h₁.seq (h₂.seq h₃)
  convert h using 1 ; simp [ a, b, transferStacks, hzero, htmp] ; omega

end SubexponentialSAT.Subexp.ScoreBuilderProgram

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

theorem overlap_le (heads : ℕ) (fixed : List (Word r Q)) (candidate : Word r Q) :
    overlap heads fixed candidate ≤ fixed.length*ReadPlan.wordWidth r Q := by
  have h := PackingHeadProgramCandidates.score_le (ReadPlan.encodeWord candidate) (headRows heads fixed)
  rw [ReadPlan.encodeWord_length,headRows_length] at h
  exact h.trans (Nat.mul_le_mul_right _ (headCount_le heads fixed))

end Scores
end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

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

abbrev CombineData := State 3 8

end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyWeights
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual native coefficient construction followed by stream weighting. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def dataLength (d : Data) : ℕ := PackingWeightProgram.inputLength
  (projectState mergeRegisters weightPorts d)

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

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

abbrev OuterData := State 16 768

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end


