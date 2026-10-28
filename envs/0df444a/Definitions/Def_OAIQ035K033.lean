-- Prove2me | Definitions.Def_OAIQ035K033
-- name    : OAIQ035K033
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T07:59:45.179464+00:00
-- url     : https://prove2.me/theorems/0cac58ed-0d35-4391-adb8-c705986b8a87
-- title:
--   Definitions bundle OAIQ035K033 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 16 declarations of OpenAI's Lean: 5 definitions, 1 inductive type or structure and 10 theorems. The definitions and types are `OAI.MetricKMedian.LPBinary.Repair.assignment`, `OAI.MetricKMedian.LPBinary.Repair.encodeData`, `OAI.MetricKMedian.Preparation.FractionalRefinement.count`, `OAI.MetricKMedian.Preparation.FractionalRefinement.original`, `OAI.MetricKMedian.Preparation.FractionalRefinement.x`, `OAI.MetricKMedian.Preparation.RationalAllParameters`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Geometry_RationalAllParameters`, `KMedian_Geometry_RationalFractionalInput`, `KMedian_Optimization_ApproximationListProgram`, `KMedian_Optimization_IntegralFractionalComparison`, `KMedian_Optimization_TruncatedObjective`, `KMedian_Rounding_RationalSignedTerminal`, `KMedian_Sparse_SparseBernoulliFeatures`, `KMedian_Sparse_SparseMarginalTools`, `KMedian_Sparse_SparseMomentAlgebra`, `KMedian_Sparse_SparseSupport`.
--
--   **Imports.** It imports the bundles `OAIQ035K016`, `OAIQ035K017`, `OAIQ035K021` and `OAIQ035K022` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K042`, `OAIQ035K043` and `OAIQ035K044`; the statement `OAI.MetricKMedian.Preparation.exists_rational_all_parameters`; the proof of `OAI.MetricKMedian.Preparation.exists_rational_all_parameters`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ035K016
import Definitions.Def_OAIQ035K017
import Definitions.Def_OAIQ035K021
import Definitions.Def_OAIQ035K022

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalAllParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Preparation

structure RationalAllParameters (η τ : ℝ) where
  round : FixedBatch.RationalParameters τ
  even : Even round.Δ
  M : ℚ
  δ : ℚ
  γ : ℚ
  T₁ : ℚ
  hM : 0<M
  hδ : 0<δ
  hδ1 : (δ:ℝ)≤1/4
  hγ : 0<γ
  hγ1 : γ≤1
  hT : 0<T₁
  hθ : 1/((M:ℝ)*(δ:ℝ))≤1/8
  hα : (M:ℝ)/((δ:ℝ)*(T₁:ℝ))≤1/4
  failure : failureFactor (γ:ℝ) (round.g:ℝ)<1
  error : max (farFactor (δ:ℝ) (1-1/((M:ℝ)*(δ:ℝ)))
              ((M:ℝ)/((δ:ℝ)*(T₁:ℝ))) ((M:ℝ)/(T₁:ℝ)) (γ:ℝ))
          (nearFactor (1-1/((M:ℝ)*(δ:ℝ))) ((M:ℝ)+(1+(δ:ℝ))*(T₁:ℝ)) (γ:ℝ) (round.g:ℝ)) /
          (1-failureFactor (γ:ℝ) (round.g:ℝ)) ≤ 1+η

end MetricKMedian.Preparation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_TruncatedObjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.TruncatedLP
open Finset
variable {ι κ : Type} [Fintype ι] [Fintype κ]

theorem objective_le_assignment (d : κ → ι → ℚ) (y : ι → ℚ) (x : κ → ι → ℚ)
    (H : ℚ) (hx : ∀ j i, 0 ≤ x j i ∧ x j i ≤ y i) (hs : ∀ j, ∑ i, x j i=1) :
    objective d y H ≤ ∑ j, ∑ i, x j i*truncated d H j i :=
  sum_le_sum (fun j _ => FractionalDual.value_le_assignment _ _ _ _ (hx j) (hs j))

end MetricKMedian.TruncatedLP
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_IntegralFractionalComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.TruncatedLP
open Finset ProjectedSubgradient
variable {n m : ℕ} [NeZero n] [NeZero m]

omit [NeZero n] [NeZero m] in

theorem integral_comparison (d : Fin m → Fin n → ℚ) (k : ℕ)
    (hd : ∀ j i, 0 ≤ d j i) (S : Finset (Fin n)) (hS : S.Nonempty)
    (hSk : S.card ≤ k) (a : Fin m → Fin n) (ha : ∀ j, a j ∈ S)
    (hc : (∑ j, d j (a j)) ≤ 1) (H : ℚ) :
    ∃ z : Fin n → ℚ, feasible (k:ℚ) z ∧ objective d z H ≤ ∑ j, d j (a j) := by
  classical
  obtain ⟨i₀,hi₀⟩ := hS
  let z : Fin n → ℚ := fun i => (if i ∈ S then 1 else 0)+
    (if i=i₀ then (k:ℚ)-(S.card:ℚ) else 0)
  have hrest : (0:ℚ) ≤ (k:ℚ)-(S.card:ℚ) := by
    have hh : (S.card:ℚ) ≤ k := by exact_mod_cast hSk
    linarith
  have hz0 : ∀ i, 0 ≤ z i := by
    intro i
    dsimp [z]
    split_ifs <;> linarith
  have hzs : (∑ i, z i)=(k:ℚ) := by
    simp only [z,sum_add_distrib,sum_ite_mem,sum_const,nsmul_eq_mul,
      sum_ite_eq',mem_univ,ite_true]
    simp
  have hza : ∀ j, 1 ≤ z (a j) := by
    intro j
    dsimp [z]
    rw [ite_eq_left (ha j)]
    split_ifs <;> linarith
  let x : Fin m → Fin n → ℚ := fun j i => if i=a j then 1 else 0
  have hx : ∀ j i, 0 ≤ x j i ∧ x j i ≤ z i := by
    intro j i
    dsimp [x]
    by_cases he : i=a j
    · rw [ite_eq_left he,he]; exact ⟨by norm_num,hza j⟩
    · rw [ite_eq_right he]; exact ⟨le_rfl,hz0 i⟩
  have hs : ∀ j, ∑ i, x j i=1 := by intro j; simp [x]
  have edge : ∀ j, d j (a j) ≤ 1 := by
    intro j
    exact (single_le_sum (fun j _ => hd j (a j)) (mem_univ j)).trans hc
  refine ⟨z,⟨hz0,hzs⟩,(objective_le_assignment d z x H hx hs).trans_eq ?_⟩
  apply sum_congr rfl
  intro j _
  simp only [x,ite_mul,one_mul,zero_mul,sum_ite_eq',mem_univ,ite_true,
    truncated,ite_eq_left (edge j)]

end MetricKMedian.TruncatedLP
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalFractionalInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.Preparation
open Finset
variable {f j : ℕ}

 theorem computedNearest_ordered (y d : Fin f → ℚ) (hy : ∀ i, 0≤y i) (hm : 1≤∑ i, y i)
    (a b : Fin f) (ha : 0<(computedNearest y d hy hm)[a.val])
    (hb : (computedNearest y d hy hm)[b.val]<y b) : d a≤d b := by
  simp only [computedNearest,Vector.getElem_ofFn] at ha hb
  exact (fill univ y d 1 (fun i _ => hy i) (by norm_num) hm).ordered a (mem_univ _)
    b (mem_univ _) ha hb

namespace FractionalRefinement

variable (a : TruncatedLP.FractionalData f j) (k : ℕ) (ha : a.Valid k) (hj : 0<j)

def x (dc : Fin j → Fin f → ℚ) (c : Fin j) (i : Fin f) : ℚ :=
  (computedNearest (y a) (dc c) (fun b => (ha.1 b).1) (mass_one a k ha hj))[i.val]

def count (dc : Fin j → Fin f → ℚ) : ℕ :=
  RationalSplitting.count (y a) (x a k ha hj dc)

def original (dc : Fin j → Fin f → ℚ) : Fin (count a k ha hj dc) → Fin f :=
  RationalSplitting.original (y a) (x a k ha hj dc)

end FractionalRefinement
end MetricKMedian.Preparation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_ApproximationListProgram
attribute [-instance] _root_.OAI.MetricKMedian.TruncatedLP.instDecidableValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset
namespace Repair
def assignment (ds xs : Row) : Row := let ws := weights ds xs; ws.map (fun w => w/ws.sum)

def encodeData {n m : ℕ} (a : TruncatedLP.FractionalData n m) : Output :=
  (List.ofFn (ProjectedSubgradient.point a.opening),List.ofFn (fun j => List.ofFn (ProjectedSubgradient.point a.assignment[j.val])))

end Repair
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseBernoulliFeatures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseBernoulli
open Finset
variable {n d : ℕ}

theorem monomial_endpoint (q : Fin n → Bool) (f : Fin d → Fin (n+1))
    (i : Fin n) (b : Fin 2) :
    monomial (endpoint q i b) f=
      if i ∈ used f then (if b=0 then 1 else 0)*monomial q (without f i)
      else monomial q f := by
  by_cases hi : i ∈ used f
  · rw [ite_eq_left hi]
    unfold monomial
    rw [used_without,← mul_prod_erase (used f) (flag (endpoint q i b)) hi]
    rw [flag_endpoint,ite_eq_left rfl]
    congr 1
    apply prod_congr rfl
    intro x hx
    rw [flag_endpoint,ite_eq_right (mem_erase.mp hx).1]
  · rw [ite_eq_right hi]
    unfold monomial
    apply prod_congr rfl
    intro x hx
    rw [flag_endpoint,ite_eq_right (fun (he : x=i) => hi (he ▸ hx))]

theorem target_succ (p : Fin n → ℚ) (t : ℕ) (ht : t<n) (f : Fin d → Fin (n+1)) :
    target p (t+1) f=
      if (⟨t,ht⟩ : Fin n) ∈ used f then p ⟨t,ht⟩*target p t (without f ⟨t,ht⟩)
      else target p t f := by
  let i : Fin n := ⟨t,ht⟩
  have val_ne : ∀ x : Fin n, x ≠ i → x.val ≠ t := fun x h he => h (Fin.ext he)
  by_cases hi : i ∈ used f
  · rw [ite_eq_left hi]
    unfold target
    rw [used_without,← mul_prod_erase (used f) (fun x => if x.val<t+1 then p x else 0) hi]
    simp only [i,show t<t+1 by omega,ite_eq_left]
    congr 1
    apply prod_congr rfl
    intro x hx
    have hn := val_ne x (mem_erase.mp hx).1
    have he : x.val<t+1 ↔ x.val<t := by omega
    simp only [he]
  · rw [ite_eq_right hi]
    unfold target
    apply prod_congr rfl
    intro x hx
    have hn := val_ne x (fun (he : x=i) => hi (he ▸ hx))
    have he : x.val<t+1 ↔ x.val<t := by omega
    simp only [he]

end MetricKMedian.SparseBernoulli

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseMarginalTools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α : Type}

 theorem moment_congr (μ : SparseIntegerLaw α) (f g : α → ℚ)
    (h : ∀ i : Fin μ.length, f μ.states[i.val]=g μ.states[i.val]) :
    μ.moment f=μ.moment g := by
  apply sum_congr rfl
  intro i _
  rw [h i]

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseMomentAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α : Type}

theorem moment_mul (μ : SparseIntegerLaw α) (c : ℚ) (f : α → ℚ) :
    μ.moment (fun a => c*f a)=c*μ.moment f := by
  simp only [moment,mul_left_comm,mul_sum]

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α : Type}

theorem zero_indicator (μ : SparseIntegerLaw α) (P : α → Prop) [DecidablePred P]
    (hz : μ.moment (fun x => if P x then 1 else 0)=0)
    (a : Fin μ.length) (ha : 0 < μ.law.rational.weight a) : ¬P μ.states[a.val] := by
  intro hpa
  have hs := single_le_sum (s := univ)
    (f := fun i : Fin μ.length => μ.law.rational.weight i*(if P μ.states[i.val] then 1 else 0))
    (fun i _ => mul_nonneg (μ.law.rational.nonneg _) (by split_ifs <;> norm_num)) (mem_univ a)
  change _ ≤ μ.moment (fun x => if P x then 1 else 0) at hs
  rw [hz,ite_eq_left hpa,mul_one] at hs
  exact (not_lt_of_ge hs) ha

theorem one_indicator (μ : SparseIntegerLaw α) (P : α → Prop) [DecidablePred P]
    (hz : μ.moment (fun x => if P x then 1 else 0)=1)
    (a : Fin μ.length) (ha : 0 < μ.law.rational.weight a) : P μ.states[a.val] := by
  by_contra hn
  have hs := single_le_sum (s := univ)
    (f := fun i : Fin μ.length => μ.law.rational.weight i*(if P μ.states[i.val] then 0 else 1))
    (fun i _ => mul_nonneg (μ.law.rational.nonneg _) (by split_ifs <;> norm_num)) (mem_univ a)
  have hsum : (∑ i : Fin μ.length, μ.law.rational.weight i*(if P μ.states[i.val] then 0 else 1))=0 := by
    have hh : ∀ i : Fin μ.length,
        μ.law.rational.weight i*(if P μ.states[i.val] then 0 else 1)=
          μ.law.rational.weight i-μ.law.rational.weight i*(if P μ.states[i.val] then 1 else 0) := by
      intro i
      split_ifs <;> ring
    simp_rw [hh]
    rw [sum_sub_distrib,μ.law.rational.total]
    change 1-μ.moment (fun x => if P x then 1 else 0)=0
    rw [hz,sub_self]
  rw [hsum,ite_eq_right hn,mul_one] at hs
  exact (not_lt_of_ge hs) ha

end MetricKMedian.SparseIntegerLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalSignedTerminal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalSignedTerminal
open Finset RationalWeightedStep RationalSignedStep
variable {n : ℕ}

theorem state_spec (u : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1)
    (hu : ∀ i, 0 < u i → u i ≤ 1) (hpair : ¬Active u p)
    (ω : Fin n → Bool)
    (hfixed : ∀ i, i∉fractional p → SparseBernoulli.flag ω i=point p i) :
    (∀ i, 0 ≤ point (state u p ω) i ∧ point (state u p ω) i ≤ 1) ∧
    (fractional (state u p ω)).card ≤ 1 ∧
    (∑ i, u i*point (state u p ω) i) ≤ (∑ i, u i*point p i)+1 := by
  let P := (fractional p).filter (fun i => 0 < u i)
  let N := (fractional p).filter (fun i => u i < 0)
  have hP : P.card ≤ 1 := by
    apply card_le_one.mpr
    intro i hi j hj
    by_contra hij
    exact inactive u p hpair i (mem_filter.mp hi).1 j (mem_filter.mp hj).1 hij
      (mul_pos (mem_filter.mp hi).2 (mem_filter.mp hj).2)
  have hN : N.card ≤ 1 := by
    apply card_le_one.mpr
    intro i hi j hj
    by_contra hij
    exact inactive u p hpair i (mem_filter.mp hi).1 j (mem_filter.mp hj).1 hij
      (mul_pos_of_neg_of_neg (mem_filter.mp hi).2 (mem_filter.mp hj).2)
  have hq : ∀ i, 0 ≤ point (state u p ω) i ∧ point (state u p ω) i ≤ 1 := by
    intro i
    rw [point_state]
    split_ifs
    · exact hp i
    · cases hω : ω i <;> simp [SparseBernoulli.flag,hω]
  refine ⟨hq,?_,?_⟩
  · apply le_trans (card_le_card (show fractional (state u p ω) ⊆ N from ?_)) hN
    intro i hi
    have hneg : u i<0 := by
      by_contra hn
      have hh := (mem_filter.mp hi).2
      simp only [point_state,ite_eq_right hn] at hh
      cases hω : ω i <;> simp [SparseBernoulli.flag,hω] at hh
    exact mem_filter.mpr ⟨by
      simpa only [fractional,mem_filter,mem_univ,true_and,point_state,ite_eq_left hneg] using hi,hneg⟩
  · have hz : ∀ i, i ∉ P → u i*(point (state u p ω) i-point p i)=0 := by
      intro i hi
      by_cases hn : u i<0
      · simp only [point_state,ite_eq_left hn,sub_self,mul_zero]
      by_cases he : u i=0
      · rw [he,zero_mul]
      have hp' : 0 < u i := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm he)
      have hnf : i ∉ fractional p := fun hf => hi (mem_filter.mpr ⟨hf,hp'⟩)
      simp only [point_state,ite_eq_right hn,hfixed i hnf,sub_self,mul_zero]
    have ht : ∀ i ∈ P, u i*(point (state u p ω) i-point p i) ≤ 1 := by
      intro i hi
      have hui := (mem_filter.mp hi).2
      calc
        _ ≤ u i*1 := mul_le_mul_of_nonneg_left (by linarith only [(hq i).2,(hp i).1]) hui.le
        _ ≤ 1 := by simpa only [mul_one] using hu i hui
    have hsum : (∑ i, u i*(point (state u p ω) i-point p i)) ≤ 1 := by
      rw [← sum_subset (subset_univ P) (fun i _ hi => hz i hi)]
      calc
        _ ≤ ∑ _i ∈ P, (1:ℚ) := sum_le_sum ht
        _ = (P.card:ℚ) := by simp only [sum_const,nsmul_eq_mul,mul_one]
        _ ≤ 1 := by exact_mod_cast hP
    simp only [mul_sub,sum_sub_distrib] at hsum
    linarith only [hsum]

end MetricKMedian.RationalSignedTerminal
end
end

end OAI
end


