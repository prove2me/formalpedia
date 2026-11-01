-- Prove2me | Definitions.Def_OAIQ053K032
-- name    : OAIQ053K032
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:00:40.756413+00:00
-- url     : https://prove2.me/theorems/d67ffae0-742f-4f0e-a5ba-724c0913313a
-- title:
--   Definitions bundle OAIQ053K032 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 67 declarations of OpenAI's Lean: 32 definitions, 5 inductive types or structures and 30 theorems. The definitions and types are `OAI.MetricKMedian.CopyState.State`, `OAI.MetricKMedian.CopyState.Valid`, `OAI.MetricKMedian.CopyState.advance`, `OAI.MetricKMedian.CopyState.forcedAlive`, `OAI.MetricKMedian.CopyState.forcedGroups`, `OAI.MetricKMedian.CopyState.roundAlive`, `OAI.MetricKMedian.FixedBatch.RationalParameters.CopyNearestProgram.instLinearOrderCopyFin`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.QData`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.RationalInput`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.eqm`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.eqr`, `OAI.MetricKMedian.RationalPhysicalKernel.HistoryProgram.Hist`, `OAI.MetricKMedian.RationalPhysicalKernel.UpdateProgram.Input.update`, `OAI.MetricKMedian.RoundingList.er`, `OAI.MetricKMedian.RoundingProgram.Input.start`, `OAI.MetricKMedian.RoundingProgram.State`, `OAI.MetricKMedian.RoundingProgram.State.branch`, `OAI.MetricKMedian.RoundingProgram.erow`, `OAI.MetricKMedian.SparseBernoulli.Program.Input.encode`, `OAI.MetricKMedian.SparseBernoulli.Program.qr`, `OAI.MetricKMedian.SparseCardinalRounding.Program.br`, `OAI.MetricKMedian.SparseCardinalRounding.Program.encodeInput`, `OAI.MetricKMedian.SparseGraph.ListOperation.er`, `OAI.MetricKMedian.SparseGraph.ListOperation.et`, `OAI.MetricKMedian.SparseGraph.ListOperation.view`, `OAI.MetricKMedian.SparseGraph.Program.Context`, `OAI.MetricKMedian.SparseGraph.Program.Input`, `OAI.MetricKMedian.SparseGraph.Program.QInput.encode`, `OAI.MetricKMedian.SparseGraph.Program.State`, `OAI.MetricKMedian.SparseGraph.Program.T`, `OAI.MetricKMedian.SparseGraph.Program.eqi`, `OAI.MetricKMedian.SparseGraph.Program.qr`, `OAI.MetricKMedian.SparseGraph.Program.qt`, `OAI.MetricKMedian.SparseIntegerLaw.BinarySparse.raw`, `OAI.MetricKMedian.SparseIntegerLaw.DependentProgram.Bundle`, `OAI.MetricKMedian.SparseIntegerLaw.DependentProgram.Bundle.raw`, `OAI.MetricKMedian.TaperGraphProgram.Input.qInput`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Geometry_GraphListOperations`, `KMedian_Geometry_IntegerBranching`, `KMedian_Preparation_PreparationMoments`, `KMedian_Preparation_RationalRepresentatives`, `KMedian_Probability_BernoulliStepProgram`, `KMedian_Probability_PushforwardLaw`, `KMedian_Process_CopyNearestProgram`, `KMedian_Process_PhysicalBatchUpdateProgram`, `KMedian_Process_PhysicalHistoriesProgram`, `KMedian_Process_PhysicalRound`, `KMedian_Process_PhysicalState`, `KMedian_Process_RoundingCoordinateHeight`, `KMedian_Process_RoundingListOperations`, `KMedian_Process_RoundingRunProgram`, `KMedian_Process_RoundingUniformStep`, `KMedian_Process_StateInvariants`, `KMedian_Process_TaperGraphProgram`, `KMedian_Process_TaperReindex`, `KMedian_Programs_CardinalRoundProgram`, `KMedian_Programs_DependentSparseProgram`, `KMedian_Programs_GraphLawProgram`, `KMedian_Programs_GraphStepProgram`, `KMedian_Programs_RationalFeatureProgram`, `KMedian_Rounding_RationalWeightedInvariants`, `KMedian_Sparse_SparseIterationHeight`, `KMedian_Sparse_SparseListTrim`, `KMedian_Sparse_SparseMapBind`.
--
--   **Imports.** It imports the bundles `OAIQ053K014`, `OAIQ053K015`, `OAIQ053K016`, `OAIQ053K017`, `OAIQ053K018` and `OAIQ053K019` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K040`, `OAIQ053K041`, `OAIQ053K042` and `OAIQ053K043`; the statements `OAI.MetricKMedian.CopyState.rational_conditional_round_drift_s53`, `OAI.MetricKMedian.CopyState.valid_advance_s53` and `OAI.MetricKMedian.RationalBatchData.proposal_survival_s53`; the proofs of `OAI.MetricKMedian.CopyState.rational_conditional_round_drift_s53`, `OAI.MetricKMedian.CopyState.valid_advance_s53`, `OAI.MetricKMedian.FixedBatch.RationalParameters.roundCounts_spec_s53`, `OAI.MetricKMedian.Preparation.physical_old_estimates_s53` and `OAI.MetricKMedian.RationalBatchData.proposal_survival_s53`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K014
import Definitions.Def_OAIQ053K015
import Definitions.Def_OAIQ053K016
import Definitions.Def_OAIQ053K017
import Definitions.Def_OAIQ053K018
import Definitions.Def_OAIQ053K019

section
-- module Solutions.OAIQ053_KM.KMedian_Process_RoundingListOperations
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.RoundingList
open Binary Binary.Automatic Binary.Automatic.Poly RationalWeightedStep Finset
abbrev er := encodeList Ratio.encode

theorem probability_list {n : ℕ} (β : Fin n → ℚ) (p : Vector ℚ n) :
    probability (List.ofFn β) p.toList=RationalWeightedStep.probability β p := by
  unfold probability RationalWeightedStep.probability
  rw [active_list]
  simp only [decide_eq_true_eq]
  split_ifs with h
  · simp only [ratio,first_list p h,second_list p h,Gaussian.ListOperation.get_ofFn,up_list,down_list]
  · rfl

theorem endpoint_list {n : ℕ} (β : Fin n → ℚ) (p : Vector ℚ n) (b : Fin 2) :
    endpoint (List.ofFn β) p.toList (decide (b≠0))=(RationalWeightedStep.endpoint β p b).toList := by
  unfold endpoint RationalWeightedStep.endpoint
  rw [active_list]
  simp only [decide_eq_true_eq]
  by_cases h : 1<(RationalWeightedStep.fractional p).card
  · simp only [ite_eq_left h,dite_eq_left h,ratio,first_list p h,second_list p h,Gaussian.ListOperation.get_ofFn,up_list,down_list]
    by_cases hb : b=0 <;> simp [hb,move_list]
  · simp only [ite_eq_right h,dite_eq_right h]

end MetricKMedian.RoundingList
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalWeightedInvariants
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalWeightedStep
open Finset
variable {n : ℕ}

theorem endpoint_feasible (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (p : Vector ℚ n) (hp : ∀ k, 0 ≤ point p k ∧ point p k ≤ 1) (b : Fin 2) :
    ∀ k, 0 ≤ point (endpoint β p b) k ∧ point (endpoint β p b) k ≤ 1 := by
  by_cases h : 1 < (fractional p).card
  · let a := pair p h
    let r := β a.val.1/β a.val.2
    have hr : 0 < r := div_pos (hβ _) (hβ _)
    have hu := up_pos p _ _ r hr a.property.1 a.property.2.1
    have hd := down_pos p _ _ r hr a.property.1 a.property.2.1
    have hpr0 : ∀ k, 0 ≤ realPoint p k := fun k => by
      dsimp only [realPoint]; exact_mod_cast (hp k).1
    have hpr1 : ∀ k, realPoint p k ≤ 1 := fun k => by
      dsimp only [realPoint]; exact_mod_cast (hp k).2
    have hrr : (0:ℝ) < r := by exact_mod_cast hr
    let t := if b=0 then up p a.val.1 a.val.2 r else -down p a.val.1 a.val.2 r
    have ht0 : -down p a.val.1 a.val.2 r ≤ t := by dsimp only [t]; split_ifs <;> linarith
    have ht1 : t ≤ up p a.val.1 a.val.2 r := by dsimp only [t]; split_ifs <;> linarith
    have ht0r : -WeightedRounding.down (realPoint p) a.val.1 a.val.2 (r:ℝ) ≤ (t:ℝ) := by
      rw [← real_down,← Rat.cast_neg]; exact_mod_cast ht0
    have ht1r : (t:ℝ) ≤ WeightedRounding.up (realPoint p) a.val.1 a.val.2 (r:ℝ) := by
      rw [← real_up]; exact_mod_cast ht1
    have hh := WeightedRounding.move_bounds hpr0 hpr1 a.property.2.2 hrr ht0r ht1r
    rw [← real_move] at hh
    simp only [realPoint] at hh
    intro k
    simp only [endpoint,dite_eq_left h]
    exact ⟨by exact_mod_cast hh.1 k,by exact_mod_cast hh.2 k⟩
  · simpa only [endpoint,dite_eq_right h] using hp

theorem endpoint_smaller (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (p : Vector ℚ n) (h : 1 < (fractional p).card) (b : Fin 2) :
    (fractional (endpoint β p b)).card < (fractional p).card := by
  let a := pair p h
  let r := β a.val.1/β a.val.2
  have hr : (0:ℝ) < r := by exact_mod_cast div_pos (hβ a.val.1) (hβ a.val.2)
  have hi : a.val.1 ∈ MarginalRounding.fractional (realPoint p) := by
    rw [real_fractional]; exact a.property.1
  have hj : a.val.2 ∈ MarginalRounding.fractional (realPoint p) := by
    rw [real_fractional]; exact a.property.2.1
  simp only [endpoint,dite_eq_left h]
  by_cases hb : b=0
  · rw [ite_eq_left hb]
    have hh := WeightedRounding.up_smaller hr a.property.2.2 hi hj
    simpa only [← real_up,← real_move,real_fractional] using hh
  · rw [ite_eq_right hb]
    have hh := WeightedRounding.down_smaller hr a.property.2.2 hi hj
    simpa only [← real_down,← Rat.cast_neg,← real_move,real_fractional] using hh

end MetricKMedian.RationalWeightedStep
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_IntegerBranching
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.IntegerBranching
open Finset
variable {n : ℕ}

theorem branch_denominator (μ : IntegerLaw (Fin n)) (p : Fin n → ℚ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (L : ℕ)
    (hden : ∀ i, ((p i).den:ℤ) ≤ (2:ℤ)^L) :
    (branch μ p hp).denominator ≤ μ.denominator*(2:ℤ)^(L*n) := by
  apply mul_le_mul_of_nonneg_left _ μ.denominator_pos.le
  simpa only [Fintype.card_fin] using RationalScaling.denominator_bound p L hden

end MetricKMedian.IntegerBranching

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_RationalFeatureProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.IntegerLaw.BinaryCompression
open Binary Binary.PolyProgram Function
abbrev eqr := encodeList Ratio.encode
abbrev eqm := encodeList eqr
abbrev QData := List Unit × (LawData × QRows)

structure RationalInput where
  n : ℕ
  d : ℕ
  μ : IntegerLaw (Fin n)
  v : Fin n → Fin d → ℚ

end MetricKMedian.IntegerLaw.BinaryCompression
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseListTrim
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
attribute [-simp] _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.SparseIntegerLaw.BinarySparse
open Binary Binary.PolyProgram Function Finset
variable {α : Type}

def raw (μ : SparseIntegerLaw α) : Data α :=
  ((μ.law.denominator,List.ofFn μ.law.numerator),μ.states.toList)

theorem states_list (μ : SparseIntegerLaw α) : μ.states.toList=List.ofFn (fun i : Fin μ.length => μ.states[i.val]) := by
  apply List.ext_getElem <;> intros <;> simp

end MetricKMedian.SparseIntegerLaw.BinarySparse
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_RoundingUniformStep
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
attribute [-simp] _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.BinarySparse
abbrev erow := RoundingList.er

structure State (signed : Bool) where
  n : ℕ
  β : Fin n → ℚ
  positive : signed=false → ∀ i, 0<β i
  μ : SparseIntegerLaw (Vector ℚ n)

theorem encodeList_map {α β : Type} (eb : β → List Bool) (f : α → β) (xs : List α) :
    encodeList eb (xs.map f)=encodeList (fun x => eb (f x)) xs := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons, encodeList,ih]

def State.branch {s : Bool} (x : State s) : State s :=
  { x with μ := (if hs : s=true then
      x.μ.branch (RationalSignedStep.probability x.β) (RationalSignedStep.probability_unit x.β) (RationalSignedStep.endpoint x.β)
      else x.μ.branch (RationalWeightedStep.probability x.β)
        (RationalWeightedStep.probability_unit x.β (x.positive (by simpa using hs))) (RationalWeightedStep.endpoint x.β)) }

end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_GraphListOperations
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseGraph.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly
abbrev er := encodeList encodeBool
abbrev et := encodeList er

def view {n m : ℕ} (G : Graph n m) : Table := List.ofFn (fun i => List.ofFn (fun h => decide (h∈G i)))
end MetricKMedian.SparseGraph.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_PreparationMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteLaw
open Finset
variable {Ω I : Type*} [Fintype Ω] [Fintype I]

theorem variance_sum_le (μ : FiniteLaw Ω) (X : I → Ω → ℝ) (q v : I → ℝ)
    (hmean : ∀ i, μ.expect (X i)=q i)
    (hvar : ∀ i, μ.variance (X i) ≤ v i)
    (hpair : ∀ i j, i ≠ j → μ.expect (fun ω => X i ω*X j ω) ≤ q i*q j) :
    μ.variance (fun ω => ∑ i, X i ω) ≤ ∑ i, v i := by
  classical
  have hs : μ.expect (fun ω => (∑ i, X i ω)^2) ≤ (∑ i, q i)^2+∑ i, v i := by
    have hp : ∀ i j, μ.expect (fun ω => X i ω*X j ω) ≤ q i*q j+(if i=j then v i else 0) := by
      intro i j
      by_cases h : i=j
      · subst j
        have hv := hvar i
        rw [variance_eq, hmean i] at hv
        simpa only [ite_true, sq] using (by linarith only [hv] : μ.expect (fun ω => (X i ω)^2) ≤ q i^2+v i)
      · simpa only [ite_eq_right h, add_zero] using hpair i j h
    calc
      _ = ∑ i, ∑ j, μ.expect (fun ω => X i ω*X j ω) := by
        simp_rw [sq, sum_mul_sum, expect_sum]
      _ ≤ ∑ i, ∑ j, (q i*q j+if i=j then v i else 0) :=
        sum_le_sum (fun i _ => sum_le_sum (fun j _ => hp i j))
      _ = _ := by
        simp only [sum_add_distrib, sum_ite_eq, mem_univ, ite_true, ← mul_sum, ← sum_mul, sq]
  rw [variance_eq, expect_sum]
  simp only [hmean] at *
  linarith only [hs]

omit [Fintype I] in
 theorem variance_mul (μ : FiniteLaw Ω) (X : Ω → ℝ) (g : ℝ) :
    μ.variance (fun ω => g*X ω)=g^2*μ.variance X := by
  rw [variance_eq, variance_eq, expect_mul]
  simp_rw [mul_pow, expect_mul]
  ring

end MetricKMedian.FiniteLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_RationalRepresentatives
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.Preparation.RationalRepresentatives
open Finset
variable {n : ℕ}

theorem select_spec (d : Fin n → Fin n → ℚ) (V : Fin n → ℚ) (M : ℚ)
    (hd0 : ∀ j, d j j=0) (hds : ∀ i j, d i j=d j i) (hM : 0 ≤ M)
    (k : ℕ) (U : Finset (Fin n)) (hk : U.card ≤ k) (hV : ∀ j ∈ U, 0 ≤ V j) :
    select d V M k U ⊆ U ∧
      (↑(select d V M k U) : Set (Fin n)).Pairwise
        (fun s t => M*max (V s) (V t) < d s t) ∧
      ∀ j ∈ U, ∃ s ∈ select d V M k U, V s ≤ V j ∧ d j s ≤ M*V j := by
  induction k generalizing U with
  | zero =>
      have he : U=∅ := card_eq_zero.mp (Nat.eq_zero_of_le_zero hk)
      simp [select, he]
  | succ k ih =>
      by_cases hU : U.Nonempty
      · let s := firstNearest U V hU
        have hs : s ∈ U := (firstNearest_spec U V hU).1
        have hmin : ∀ j ∈ U, V s ≤ V j := (firstNearest_spec U V hU).2
        let W := U.filter (fun j => M*V j < d j s)
        have hWU : W ⊆ U := filter_subset _ _
        have hsW : s ∉ W := by
          intro hh
          have h := (mem_filter.mp hh).2
          rw [hd0] at h
          exact not_lt_of_ge (mul_nonneg hM (hV s hs)) h
        have hwk : W.card ≤ k := by
          have hproper : W ⊂ U := Finset.ssubset_iff_subset_ne.mpr ⟨hWU, fun he => hsW (he ▸ hs)⟩
          have hc := card_lt_card hproper
          omega
        obtain ⟨hsub,hpair,hcover⟩ := ih W hwk (fun j hj => hV j (hWU hj))
        simp only [select, dite_eq_left hU]
        change insert s (select d V M k W) ⊆ U ∧ _
        refine ⟨insert_subset hs (hsub.trans hWU), ?_, ?_⟩
        · intro a ha b hb hab
          rcases mem_insert.mp ha with rfl | ha
          · have hb' := (mem_insert.mp hb).resolve_left (Ne.symm hab)
            have hbW := hsub hb'
            rw [max_eq_right (hmin b (hWU hbW)),hds]
            exact (mem_filter.mp hbW).2
          · rcases mem_insert.mp hb with rfl | hb
            · have haW := hsub ha
              rw [max_eq_left (hmin a (hWU haW))]
              exact (mem_filter.mp haW).2
            · exact hpair ha hb hab
        · intro j hj
          by_cases hjW : j ∈ W
          · obtain ⟨a,ha,hv,hd⟩ := hcover j hjW
            exact ⟨a,mem_insert_of_mem ha,hv,hd⟩
          · exact ⟨s,mem_insert_self _ _,hmin j hj,
              le_of_not_gt (fun h => hjW (mem_filter.mpr ⟨hj,h⟩))⟩
      · have he := not_nonempty_iff_eq_empty.mp hU
        simp [select, he]

theorem representatives_spec (d : Fin n → Fin n → ℚ) (V : Fin n → ℚ) (M : ℚ)
    (hd0 : ∀ j, d j j=0) (hds : ∀ i j, d i j=d j i) (hM : 0 ≤ M)
    (hV : ∀ j, 0 ≤ V j) :
    (↑(representatives d V M) : Set (Fin n)).Pairwise
        (fun s t => M*max (V s) (V t) < d s t) ∧
      ∀ j, ∃ s ∈ representatives d V M, V s ≤ V j ∧ d j s ≤ M*V j := by
  have hh := select_spec d V M hd0 hds hM n univ (by simp) (fun j _ => hV j)
  exact ⟨hh.2.1, fun j => hh.2.2 j (mem_univ _)⟩

end MetricKMedian.Preparation.RationalRepresentatives
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_DependentSparseProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.SparseIntegerLaw.DependentProgram
open Binary Binary.PolyProgram Function BinarySparse
variable {C A : Type} (T : C → Type)

structure Bundle where
  ctx : C
  law : SparseIntegerLaw (T ctx)

variable {T} (ec : C → List Bool) (ea : A → List Bool) (view : ∀ c, T c → A)

def Bundle.raw (x : Bundle T) : C × Data A :=
  (x.ctx,((x.law.law.denominator,List.ofFn x.law.law.numerator),x.law.states.toList.map (view x.ctx)))

end MetricKMedian.SparseIntegerLaw.DependentProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_BernoulliStepProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparseBernoulli.Program
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.DependentProgram
abbrev qr := encodeList Ratio.encode

abbrev Input.encode (x : Input) := qr (List.ofFn x.p)

end MetricKMedian.SparseBernoulli.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_PushforwardLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteLaw
open Finset
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ]

 theorem support_map (μ : FiniteLaw Ω) (f : Ω → Ξ) (ξ : Ξ)
    (h : 0 < (μ.map f).weight ξ) : ∃ ω, 0 < μ.weight ω ∧ f ω=ξ := by
  exact μ.property_map f (fun ξ => ∃ ω, 0 < μ.weight ω ∧ f ω=ξ)
    (fun ω hω => ⟨ω,hω,rfl⟩) ξ h

end MetricKMedian.FiniteLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalRound
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential FixedBatch
variable {F : Type*} [DecidableEq F] [Fintype F] {Δ : ℕ}

noncomputable def forcedGroups (A : Finset (Copy (F := F) Δ)) (H : Finset A) : Finset F :=
  H.image (fun i => i.val.1)

noncomputable def forcedAlive (A S : Finset (Copy (F := F) Δ)) (H : Finset A) : Finset A :=
  (localSet A S).filter (fun i => i.val.1 ∈ forcedGroups A H)

noncomputable def roundAlive (A S : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graphActions G) H)) (x g : ℝ) (d : F → ℝ) :
    Finset (Copy (F := F) Δ) :=
  (nextAliveAt (heavyActions (graphActions G) H) (Analytic.coefficient x (mass g S))
    (fun i => d i.val.1) (localSet A S \ forcedAlive A S H) Z).image Subtype.val

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalState
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential FixedBatch Analytic
variable {F J X : Type*} [Fintype F] [DecidableEq F] [Fintype J] [DecidableEq J]
variable [PseudoMetricSpace X] {Δ : ℕ}

abbrev State (F J : Type*) (Δ : ℕ) := Finset (Copy (F := F) Δ) × (J → Finset (Copy (F := F) Δ))

noncomputable def advance (s : State F J Δ) (G : s.1 → Finset s.1) (H : Finset s.1)
    (Z : Finset (HeavyAction (graphActions G) H)) (x g : ℝ)
    (d : J → F → ℝ) : State F J Δ :=
  (next Δ s.1 (roundErased s.1 G H Z) (roundOpened s.1 G H Z),
    fun j => roundAlive s.1 (s.2 j) G H Z x g (d j))

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_StateInvariants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential FixedBatch
variable {F J X : Type*} [Fintype F] [DecidableEq F] [Fintype J] [DecidableEq J]
variable [PseudoMetricSpace X] {Δ : ℕ}

def Valid (g : ℝ) (location : F → X) (client : J → X) (R : J → ℝ)
    (S₀ : J → Finset (Copy (F := F) Δ)) (s : State F J Δ) : Prop :=
  1 ≤ mass g s.1 ∧
    (∀ j, s.2 j ⊆ s.1) ∧ (∀ j, s.2 j ⊆ S₀ j) ∧
    ∀ j, (¬∃ f ∈ integral Δ s.1, dist (client j) (location f) ≤ 5*R j) → S₀ j ⊆ s.1

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_RoundingCoordinateHeight
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.RationalGrid
open Binary

theorem table {n : ℕ} (q : Fin n → ℚ) (i : Fin n) : At (RationalScaling.denominator q) (q i) := by
  refine ⟨RationalScaling.numerator q i,?_⟩
  rw [RationalScaling.numerator_cast,mul_div_cancel_right₀ _ (by exact_mod_cast (RationalScaling.denominator_pos q).ne')]

end MetricKMedian.RationalGrid

namespace MetricKMedian.RoundingHeight
open RationalGrid RationalWeightedStep Binary
variable {n : ℕ}

theorem denominator_pos (β : Fin n → ℚ) (p : Vector ℚ n) : 0<denominator β p :=
  mul_pos (RationalScaling.denominator_pos _) (RationalScaling.denominator_pos _)

theorem initial_grid (β : Fin n → ℚ) (p : Vector ℚ n) :
    (∀ i, At (denominator β p) (β i)) ∧ (∀ i, At (denominator β p) (β i*point p i)) :=
  ⟨fun i => enlarge (table β i) _ (RationalScaling.denominator_pos _).ne',
    fun i => RationalGrid.mul (table β i) (table (point p) i)⟩

theorem denominator_bound (β : Fin n → ℚ) (p : Vector ℚ n) (L : ℕ)
    (hb : ∀ i, HasHeight (β i) L) (hp : ∀ i, HasHeight (point p i) L) :
    denominator β p≤(2:ℤ)^(2*n*L) := by
  have h1 := RationalScaling.denominator_bound β L (fun i => (hb i).2)
  have h2 := RationalScaling.denominator_bound (point p) L (fun i => (hp i).2)
  simp only [Fintype.card_fin] at h1 h2
  calc
    _ ≤ (2:ℤ)^(L*n)*(2:ℤ)^(L*n) := mul_le_mul h1 h2 (RationalScaling.denominator_pos _).le (by positivity)
    _ = _ := by rw [← pow_add]; congr 1; ring

theorem coordinate_height (β : Fin n → ℚ) (p q : Vector ℚ n) (L : ℕ)
    (hb : ∀ i, HasHeight (β i) L) (hp : ∀ i, HasHeight (point p i) L)
    (hq : ∀ i, At (denominator β p) (β i*point q i))
    (hz : ∀ i, β i=0 → point q i=point p i)
    (hu : ∀ i, 0≤point q i ∧ point q i≤1) (i : Fin n) :
    HasHeight (point q i) (2*n*L+L) := by
  by_cases hi : β i=0
  · rw [hz i hi]
    exact (hp i).mono (by omega)
  have hD := denominator_pos β p
  have hd := denominator_bound β p L hb hp
  apply RationalGrid.unit_height (mul_ne_zero hD.ne' (by
      intro hz
      apply hi
      rw [← Rat.num_div_den (β i),hz,Int.cast_zero,zero_div]))
    (D := denominator β p * (β i).num)
  · rw [abs_mul,abs_of_pos hD,pow_add]
    exact mul_le_mul hd (hb i).1 (abs_nonneg _) (by positivity)
  · exact divide_weight hD.ne' hi (hq i)
  · rw [abs_of_nonneg (hu i).1]
    exact (hu i).2

end MetricKMedian.RoundingHeight
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseIterationHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section

namespace MetricKMedian.RationalWeightedStep
open Binary
variable {n : ℕ}

theorem up_height (p : Vector ℚ n) (i j : Fin n) (r : ℚ) (A B : ℕ)
    (hp : ∀ i, HasHeight (point p i) A) (hr : HasHeight r B) :
    HasHeight (up p i j r) (A+B+1) := by
  exact ((HasHeight.one 0 |>.sub (hp i)).mono (by omega)).min ((hp j |>.div hr).mono (by omega))
theorem down_height (p : Vector ℚ n) (i j : Fin n) (r : ℚ) (A B : ℕ)
    (hp : ∀ i, HasHeight (point p i) A) (hr : HasHeight r B) :
    HasHeight (down p i j r) (A+B+1) := by
  exact ((hp i).mono (by omega)).min (((HasHeight.one 0 |>.sub (hp j)).div hr).mono (by omega))
theorem probability_height (β : Fin n → ℚ) (p : Vector ℚ n) (A B : ℕ)
    (hβ : ∀ i, HasHeight (β i) B) (hp : ∀ i, HasHeight (point p i) A) :
    HasHeight (probability β p) (3*(A+2*B+1)+1) := by
  unfold probability
  split_ifs with h
  · let a := pair p h
    have hr := (hβ a.val.1).div (hβ a.val.2)
    have hu := up_height p a.val.1 a.val.2 _ A (B+B) hp hr
    have hd := down_height p a.val.1 a.val.2 _ A (B+B) hp hr
    convert hd.div (hu.add hd) using 1 <;> first | rfl | ring
  · exact HasHeight.zero _
end MetricKMedian.RationalWeightedStep

namespace MetricKMedian.RationalSignedStep
open Binary RationalWeightedStep
variable {n : ℕ}
theorem probability_height (β : Fin n → ℚ) (p : Vector ℚ n) (A B : ℕ)
    (hβ : ∀ i, HasHeight (β i) B) (hp : ∀ i, HasHeight (point p i) A) :
    HasHeight (probability β p) (3*(A+2*B+1)+1) := by
  unfold probability
  split_ifs with h
  · let a := pair β p h
    have hr := (hβ a.val.1).div (hβ a.val.2)
    have hu := up_height p a.val.1 a.val.2 _ A (B+B) hp hr
    have hd := down_height p a.val.1 a.val.2 _ A (B+B) hp hr
    convert hd.div (hu.add hd) using 1 <;> first | rfl | ring
  · exact HasHeight.zero _
end MetricKMedian.RationalSignedStep

end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_RoundingRunProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function Polynomial
open SparseIntegerLaw.BinarySparse

def Input.start {s : Bool} (x : Input s) : State s := ⟨x.n,x.β,x.positive,.dirac x.p⟩

end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_GraphStepProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.SparseGraph.Program
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.DependentProgram SparseIntegerLaw.BinarySparse
open ListOperation (Row Table er et)

structure Input where
  n : ℕ
  m : ℕ
  columns : Fin m → SparseIntegerLaw (Finset (Fin n))
structure Context where
  input : Input
  t : ℕ
abbrev T (c : Context) := Graph c.input.n c.input.m
abbrev State := Bundle T
end MetricKMedian.SparseGraph.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_CardinalRoundProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparseCardinalRounding.Program
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
abbrev encodeInput := SparseBernoulli.Program.Input.encode
abbrev br := encodeList encodeBool

end MetricKMedian.SparseCardinalRounding.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_GraphLawProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseGraph.Program
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
open SparseIntegerLaw.DependentProgram
abbrev qr := encodeList Ratio.encode
abbrev qt := encodeList qr
abbrev eqi := encodePair (encodeList (fun _ : Unit => [])) qt

abbrev QInput.encode (x : QInput) := eqi x.raw

end MetricKMedian.SparseGraph.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_TaperGraphProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.TaperGraphProgram
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseIntegerLaw.BinarySparse
 theorem source_unit {n : ℕ} (g P : ℚ) (d : Fin n → ℚ) (own : Finset (Fin n)) (Δ : ℕ) (hP : 0<P) (i : Fin n) :
    0≤Taper.sourceMarginals g P d own Δ i ∧ Taper.sourceMarginals g P d own Δ i≤1 := by
  unfold Taper.sourceMarginals
  split_ifs
  · unfold Taper.zeroMarginal; split_ifs <;> norm_num
  · exact marginal_unit _ _ _ hP

def Input.qInput (x : Input) : SparseGraph.Program.QInput :=
  ⟨x.n,x.n,(fun h i => Taper.sourceMarginals x.g x.P (x.d i) (x.own i) x.Δ h),
    fun h i => source_unit x.g x.P (x.d i) (x.own i) x.Δ x.positive h⟩
end MetricKMedian.TaperGraphProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_TaperReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                    
section
namespace MetricKMedian.Taper
open Finset
variable {I J : Type} [Fintype I] [Fintype J]

 theorem a_reindex (e : I ≃ J) (P t : ℚ) (d : J → ℚ) :
    A P (fun i => d (e i)) t=A P d t := e.sum_comp (fun j => aCoef P (d j) t)
 theorem b_reindex (e : I ≃ J) (P t : ℚ) (d : J → ℚ) :
    B P (fun i => d (e i)) t=B P d t := e.sum_comp (fun j => bCoef P (d j) t)
 theorem candidates_reindex (e : I ≃ J) (g P : ℚ) (d : J → ℚ) :
    candidates g P (fun i => d (e i))=candidates g P d := by
  simp only [candidates,breaks_reindex,a_reindex,b_reindex]
 theorem mass_reindex (e : I ≃ J) (g P t : ℚ) (d : J → ℚ) :
    rationalMass g P (fun i => d (e i)) t=rationalMass g P d t :=
  e.sum_comp (fun j => g*rationalMarginal P (d j) t)
 theorem roots_reindex (e : I ≃ J) (g P : ℚ) (d : J → ℚ) :
    rootCandidates g P (fun i => d (e i))=rootCandidates g P d := by
  simp only [rootCandidates,candidates_reindex,mass_reindex]
 theorem radius_reindex (e : I ≃ J) (g P : ℚ) (d : J → ℚ) :
    inverseRadius g P (fun i => d (e i))=inverseRadius g P d := by
  simp only [inverseRadius,roots_reindex]

variable [LinearOrder I] [LinearOrder J]
 theorem source_reindex (e : I ≃o J) (g P : ℚ) (d : J → ℚ) (own : Finset I) (Δ : ℕ) (i : I) :
    sourceMarginals g P d (own.map e.toEquiv.toEmbedding) Δ (e i)=
      sourceMarginals g P (fun j => d (e j)) own Δ i := by
  have hc : rationalColocatedMass g (fun j => d (e j))=rationalColocatedMass g d := colocated_reindex e.toEquiv g d
  have hr : inverseRadius g P (fun j => d (e j))=inverseRadius g P d := radius_reindex e.toEquiv g P d
  simp only [sourceMarginals,hc,hr]
  split_ifs
  · exact zeroMarginal_reindex e d own Δ i
  · rfl
end MetricKMedian.Taper
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_CopyNearestProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.FixedBatch.RationalParameters.CopyNearestProgram
open Finset Binary Binary.Automatic Binary.Automatic.Poly
open RationalPhysicalKernel RationalPhysicalKernel.CopyList
open SparseGraph.ListOperation (Row Table setView indices)
variable {τ : ℝ} (q : RationalParameters τ)
local instance instLinearOrderCopyFin {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder

end MetricKMedian.FixedBatch.RationalParameters.CopyNearestProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalBatchUpdateProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                  
section
namespace MetricKMedian.RationalPhysicalKernel.UpdateProgram
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Finset FixedBatch
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
open CopyList

local instance instLinearOrderCopyFin_rebbee6_1 {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
attribute [local instance] OAI.MetricKMedian.RationalPhysicalKernel.UpdateProgram.instLinearOrderSubtypeCopyFinMemFinset
abbrev Input.update (x : Input) (Z) := RationalBatchData.transition x.ctx.A x.G
  (RationalBatchData.heavySet (RationalBatchData.graphMass x.G x.ctx.g) x.ctx.β) Z

end MetricKMedian.RationalPhysicalKernel.UpdateProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseMapBind
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.SparseIntegerLaw
variable {α β γ : Type}
 theorem map_map (μ : SparseIntegerLaw α) (f : α → β) (g : β → γ) :
    (μ.map f).map g=μ.map (g ∘ f) := by
  unfold map
  simp only [Vector.map_map]
end MetricKMedian.SparseIntegerLaw
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalHistoriesProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.RationalPhysicalKernel.HistoryProgram
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Finset
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table)
open CopyList UpdateProgram

abbrev Hist (x : Context) := SparseHistories.History (State (Fin x.f) x.Δ x.g x.β)
end MetricKMedian.RationalPhysicalKernel.HistoryProgram
end

end OAI
end


