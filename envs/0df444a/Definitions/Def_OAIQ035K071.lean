-- Prove2me | Definitions.Def_OAIQ035K071
-- name    : OAIQ035K071
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:22:56.299356+00:00
-- url     : https://prove2.me/theorems/4c7289a8-e46e-4cec-a369-cc9d29c78870
-- title:
--   Definitions bundle OAIQ035K071 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 55 declarations of OpenAI's Lean: 17 definitions and 38 theorems. The definitions and types are `OAI.MetricKMedian.Reduction.Enumeration.arcpairs`, `OAI.MetricKMedian.Reduction.Enumeration.branchesData`, `OAI.MetricKMedian.Reduction.Enumeration.choicesRaw`, `OAI.MetricKMedian.Reduction.Enumeration.restrictData`, `OAI.MetricKMedian.Reduction.Program.LocalRaw`, `OAI.MetricKMedian.Reduction.Program.branchOut`, `OAI.MetricKMedian.Reduction.Program.candidatesData`, `OAI.MetricKMedian.Reduction.Program.completionData`, `OAI.MetricKMedian.Reduction.Program.deleteData`, `OAI.MetricKMedian.Reduction.Program.eligibleData`, `OAI.MetricKMedian.Reduction.Program.getDist`, `OAI.MetricKMedian.Reduction.Program.historyData`, `OAI.MetricKMedian.Reduction.Program.localData`, `OAI.MetricKMedian.Reduction.Program.pickData`, `OAI.MetricKMedian.Reduction.Program.radiiData`, `OAI.MetricKMedian.Reduction.Program.unionData`, `OAI.MetricKMedian.Reduction.Program.weightData`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Programs_BoundedEnumerationProgram`, `KMedian_Programs_BranchProgram`, `KMedian_Programs_RestrictionProgram`, `KMedian_Reduction_DeletionProgram`, `KMedian_Reduction_LocalCompletionProgram`, `KMedian_Sparse_SparseCoupledPreparation`, `KMedian_Sparse_SparseOuterLaw`, `KMedian_Sparse_SparseOuterMoments`, `KMedian_Sparse_SparsePreparedProbability`, `KMedian_Sparse_SparseSignedPreparation`, `KMedian_Sparse_SparseStarActivation`.
--
--   **Imports.** It imports the published bundle `Def_MetricKMedian`; the bundles `OAIQ035K066`, `OAIQ035K067` and `OAIQ035K068` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K073` and `OAIQ035K074`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K066
import Definitions.Def_OAIQ035K067
import Definitions.Def_OAIQ035K068

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_BoundedEnumerationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                 
section
namespace MetricKMedian.Reduction.Enumeration
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
@[fun_prop] theorem maskWord_poly : Poly maskWord := by
  unfold maskWord
  apply list_map
  · apply comp bool_any
    apply list_map <;> fun_prop
  · fun_prop
 theorem maskWord_view {n : ℕ} (T : Finset (Fin n)) (ys : List (Fin n)) :
    maskWord (setView T,ys.map Fin.val)=setView ys.toFinset := by
  simp only [maskWord,indices,setView,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_def,List.map_map,List.any_eq_true,List.mem_map,id_eq,decide_eq_true_eq,List.mem_toFinset]
  constructor
  · rintro ⟨_,⟨a,ha,rfl⟩,he⟩
    exact (Fin.ext (of_decide_eq_true he)) ▸ ha
  · intro hi
    exact ⟨true,⟨i,hi,by simp⟩,rfl⟩

def choicesRaw (c : ℕ) (T : Row) : Table :=
  (words c (Preparation.RationalUnitInput.Program.ranks T)).map (fun ys => maskWord (T,ys))
@[fun_prop] theorem choicesRaw_poly (c : ℕ) : Poly (choicesRaw c) := by unfold choicesRaw; apply list_map <;> fun_prop
 theorem choicesRaw_view {n : ℕ} (T : Finset (Fin n)) (c : ℕ) : choicesRaw c (setView T)=
    ((words c (List.ofFn (T.orderEmbOfFin rfl))).map List.toFinset).map setView := by
  unfold choicesRaw
  rw [Preparation.RationalUnitInput.Program.ranks_view]
  have hr : List.ofFn (fun a => (T.orderEmbOfFin rfl a).val)=(List.ofFn (T.orderEmbOfFin rfl)).map Fin.val := by simp only [List.map_ofFn,Function.comp_def]
  rw [hr,words_map,List.map_map,List.map_map]
  apply List.map_congr_left
  intro ys _
  exact maskWord_view T ys
end MetricKMedian.Reduction.Enumeration
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseStarActivation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseStarActivation
open Finset
variable {n m : ℕ}

theorem mean (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ)
    (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1) (e : Fin m) (i : Fin n) :
    (law D q).moment (fun S => if i∈S e then 1 else 0)=if i∈D e then q e else 0 := by
  have hh := SparseGraph.run_single (fun e => SparseTargetSubset.law (D e) (q e))
    (fun i e => if i∈D e then q e else 0) (fun i e => SparseTargetSubset.mean (D e) (hq e) i)
    m (le_refl m) i e
  simpa only [law,SparseGraph.edge,SparseGraph.target,e.isLt,ite_eq_left] using hh

theorem pair (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ)
    (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1) (e f : Fin m) (hef : e≠f) (i j : Fin n) :
    (law D q).moment (fun S => (if i∈S e then 1 else 0)*(if j∈S f then 1 else 0))=
      (if i∈D e then q e else 0)*(if j∈D f then q f else 0) := by
  have hh := SparseGraph.run_pair (fun e => SparseTargetSubset.law (D e) (q e))
    (fun i e => if i∈D e then q e else 0) (fun i e => SparseTargetSubset.mean (D e) (hq e) i)
    m (le_refl m) i j e f hef
  simpa only [law,SparseGraph.edge,SparseGraph.target,e.isLt,f.isLt,ite_eq_left] using hh

end MetricKMedian.SparseStarActivation
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseSignedPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseSignedPreparation
open Finset
open RationalWeightedStep (point fractional)
variable {n m : ℕ}

theorem kernel_target (D : Fin m → Finset (Fin n)) (q : Vector ℚ m)
    (hq : ∀ e, 0 ≤ point q e ∧ point q e ≤ 1) (e : Fin m) (i : Fin n) :
    (kernel D q hq).moment (fun z => if i∈z.2.1 e then 1 else 0)=
      if i∈D e then point q e else 0 := by
  rw [kernel,SparseIntegerLaw.prod_moment]
  apply Eq.trans ?_ (SparseStarActivation.mean D (point q) hq e i)
  apply SparseIntegerLaw.moment_congr
  intro a
  dsimp only
  by_cases hi : i∈(SparseStarActivation.law D (point q)).states[a.val] e
  all_goals simp only [hi,ite_true,ite_false]; exact SparseIntegerLaw.moment_const _ _

theorem kernel_target_pair (D : Fin m → Finset (Fin n)) (q : Vector ℚ m)
    (hq : ∀ e, 0 ≤ point q e ∧ point q e ≤ 1) (e f : Fin m) (hef : e≠f) (i j : Fin n) :
    (kernel D q hq).moment (fun z => (if i∈z.2.1 e then 1 else 0)*(if j∈z.2.1 f then 1 else 0))=
      (if i∈D e then point q e else 0)*(if j∈D f then point q f else 0) := by
  rw [kernel,SparseIntegerLaw.prod_moment]
  apply Eq.trans ?_ (SparseStarActivation.pair D (point q) hq e f hef i j)
  apply SparseIntegerLaw.moment_congr
  intro a
  dsimp only
  by_cases hi : i∈(SparseStarActivation.law D (point q)).states[a.val] e <;>
    by_cases hj : j∈(SparseStarActivation.law D (point q)).states[a.val] f
  all_goals simp only [hi,hj,ite_true,ite_false]; exact SparseIntegerLaw.moment_const _ _

theorem target (D : Fin m → Finset (Fin n)) (c : Fin m → ℚ) (p : Vector ℚ m)
    (hp : ∀ e, 0 ≤ point p e ∧ point p e ≤ 1) (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1)
    (e : Fin m) (i : Fin n) :
    (law D c p hp hc).moment (fun z => if i∈z.2.1 e then 1 else 0)=
      if i∈D e then point p e else 0 := by
  rw [law,SparseIntegerLaw.bindIndexed_moment]
  simp only [kernel_target]
  by_cases hi : i∈D e
  · simp only [ite_eq_left hi]
    exact SparseSignedRounding.round_mean _ _ _ _
  · simp only [ite_eq_right hi,mul_zero,sum_const_zero]

theorem target_pair (D : Fin m → Finset (Fin n)) (c : Fin m → ℚ) (p : Vector ℚ m)
    (hp : ∀ e, 0 ≤ point p e ∧ point p e ≤ 1) (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1)
    (e f : Fin m) (hef : e≠f) (i j : Fin n) :
    (law D c p hp hc).moment (fun z => (if i∈z.2.1 e then 1 else 0)*(if j∈z.2.1 f then 1 else 0)) ≤
      (if i∈D e then point p e else 0)*(if j∈D f then point p f else 0) := by
  rw [law,SparseIntegerLaw.bindIndexed_moment]
  simp only [kernel_target_pair _ _ _ _ _ hef]
  by_cases hi : i∈D e <;> by_cases hj : j∈D f
  · simp only [ite_eq_left hi,ite_eq_left hj]
    exact SparseSignedRounding.round_pair _ _ _ _ _ hef
  all_goals simp only [hi,hj,ite_true,ite_false,mul_zero,zero_mul,sum_const_zero,le_refl]

end MetricKMedian.SparseSignedPreparation
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseOuterLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseOuterLaw
open Finset
open RationalWeightedStep (point)
open SparseGridRounding (base fraction)
open SparseSignedPreparation (State)
variable {n m : ℕ}

theorem activation_mean (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (e : Fin m) (i : Fin n) :
    (law D c q hc hq).moment (fun z => activation D q z e i)=if i∈D e then q e else 0 := by
  unfold activation
  rw [SparseIntegerLaw.moment_add,SparseIntegerLaw.moment_const,SparseSignedPreparation.target]
  by_cases hi : i∈D e
  · simp only [ite_eq_left hi,fraction_identity]
  · simp only [ite_eq_right hi,add_zero]

theorem activation_pair (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (e f : Fin m) (hef : e≠f) (i j : Fin n) :
    (law D c q hc hq).moment (fun z => activation D q z e i*activation D q z f j) ≤
      (if i∈D e then q e else 0)*(if j∈D f then q f else 0) := by
  have hh := SparseIntegerLaw.moment_affine_pair_le (law D c q hc hq)
    (fun z => if i∈z.2.1 e then 1 else 0) (fun z => if j∈z.2.1 f then 1 else 0)
    (if i∈D e then (base q e:ℚ) else 0) (if j∈D f then (base q f:ℚ) else 0)
    (if i∈D e then point (fraction q) e else 0) (if j∈D f then point (fraction q) f else 0)
    (SparseSignedPreparation.target _ _ _ _ _ e i) (SparseSignedPreparation.target _ _ _ _ _ f j)
    (SparseSignedPreparation.target_pair _ _ _ _ _ e f hef i j)
  change (law D c q hc hq).moment (fun z => activation D q z e i*activation D q z f j) ≤ _ at hh
  by_cases hi : i∈D e <;> by_cases hj : j∈D f
  all_goals simpa only [hi,hj,ite_true,ite_false,fraction_identity,zero_add] using hh

end MetricKMedian.SparseOuterLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseOuterMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseOuterLaw
open Finset
open SparseGridRounding (base)
open SparseSignedPreparation (State)
variable {n m : ℕ}

theorem activation_real_mean (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (e : Fin m) (i : Fin n) :
    (law D c q hc hq).realIndex.expect (fun a => (activation D q (law D c q hc hq).states[a.val] e i:ℝ))=
      ((if i∈D e then q e else 0:ℚ):ℝ) := by
  exact ((law D c q hc hq).realIndex_expect (fun z => activation D q z e i)).trans
    (congrArg (fun x : ℚ => (x:ℝ)) (activation_mean D c q hc hq e i))

theorem activation_real_pair (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (e f : Fin m) (hef : e≠f) (i j : Fin n) :
    (law D c q hc hq).realIndex.expect (fun a =>
      (activation D q (law D c q hc hq).states[a.val] e i:ℝ)*
        (activation D q (law D c q hc hq).states[a.val] f j:ℝ)) ≤
      ((if i∈D e then q e else 0:ℚ):ℝ)*((if j∈D f then q f else 0:ℚ):ℝ) := by
  have hh := activation_pair D c q hc hq e f hef i j
  have he := SparseIntegerLaw.realIndex_expect (law D c q hc hq)
    (fun z => activation D q z e i*activation D q z f j)
  simp only [Rat.cast_mul] at he
  rw [he]
  exact_mod_cast hh

theorem activation_variance (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (e : Fin m) (i : Fin n) :
    (law D c q hc hq).realIndex.variance
      (fun a => (activation D q (law D c q hc hq).states[a.val] e i:ℝ)) ≤
      ((if i∈D e then q e else 0:ℚ):ℝ) := by
  apply FiniteLaw.adjacent_variance _ _
    (m := ((if i∈D e then (base q e:ℚ) else 0:ℚ):ℝ)) ?_ ?_
    (activation_real_mean D c q hc hq e i)
  · split_ifs <;> positivity
  · intro a _
    rcases activation_adjacent D c q hc hq a e i with hh | hh
    · exact Or.inl (by exact_mod_cast hh)
    · exact Or.inr (by exact_mod_cast hh)

theorem deficit_mean (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ) (g : ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (i : Fin n) :
    (law D c q hc hq).realIndex.expect (fun a => (deficit D q g (law D c q hc hq).states[a.val] i:ℝ))=
      (g:ℝ)*(targetMean D q i:ℝ) := by
  simp only [deficit,Rat.cast_mul,Rat.cast_sum,FiniteLaw.expect_mul,FiniteLaw.expect_sum,
    activation_real_mean,targetMean]

theorem deficit_variance (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ) (g : ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (i : Fin n) :
    (law D c q hc hq).realIndex.variance (fun a => (deficit D q g (law D c q hc hq).states[a.val] i:ℝ)) ≤
      (g:ℝ)^2*(targetMean D q i:ℝ) := by
  have hh := FiniteLaw.variance_sum_le (law D c q hc hq).realIndex
    (fun e a => (activation D q (law D c q hc hq).states[a.val] e i:ℝ))
    (fun e => ((if i∈D e then q e else 0:ℚ):ℝ))
    (fun e => ((if i∈D e then q e else 0:ℚ):ℝ))
    (fun e => activation_real_mean D c q hc hq e i)
    (fun e => activation_variance D c q hc hq e i)
    (fun e f hef => activation_real_pair D c q hc hq e f hef i i)
  simp only [deficit,Rat.cast_mul,Rat.cast_sum,FiniteLaw.variance_mul,targetMean]
  exact mul_le_mul_of_nonneg_left hh (sq_nonneg _)

theorem clipping_budget (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ) (g : ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e)
    (δ : Fin n → ℝ) {γ : ℝ} (hg : 0 ≤ g) (hγ : 0 < γ) (hδ : ∀ i, 0 ≤ δ i)
    (hmean : ∀ i, (g:ℝ)*(targetMean D q i:ℝ)=(1+γ)*δ i)
    (hsmall : ∀ i, (1+γ)*δ i ≤ 1/4) :
    1-4*(g:ℝ)*(1+γ)/γ ≤ (law D c q hc hq).realIndex.prob (fun a =>
      (∑ i, ((deficit D q g (law D c q hc hq).states[a.val] i:ℝ)-
        min (deficit D q g (law D c q hc hq).states[a.val] i:ℝ) (1/2))) ≤ γ*∑ i,δ i) := by
  classical
  apply FiniteLaw.clipping_budget _ _ δ (by exact_mod_cast hg) hγ hδ
  · intro i
    rw [deficit_mean,hmean]
    exact hsmall i
  · intro i
    have hh := deficit_variance D c q g hc hq i
    have he : (g:ℝ)^2*(targetMean D q i:ℝ)=(g:ℝ)*(1+γ)*δ i := by
      rw [pow_two,mul_assoc,hmean]
      ring
    exact hh.trans_eq he

end MetricKMedian.SparseOuterLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparsePreparedProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparsePrepared
open Finset SparseOuterLaw
open SparseSignedPreparation (State)
variable {n m : ℕ}

theorem total_deviation (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ) (Δ : ℕ)
    (hc : ∀ e,0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e,0 ≤ q e) (g : ℚ)
    (p δ : Fin n → ℝ) {γ : ℝ} (hg : 0 < g) (hγ : 0 ≤ γ)
    (heven : Even Δ) (hunit : g*(Δ:ℚ)=1) (hδ : ∀ j,0 ≤ δ j)
    (hδhalf : ∀ j,δ j ≤ 1/2) (hp : ∀ j,p j+δ j=1)
    (hmean : ∀ j,(g:ℝ)*(targetMean D q j:ℝ)=(1+γ)*δ j) (j : Fin n) :
    (SparseOuterLaw.law D c q hc hq).realIndex.expect (fun a =>
      |(g:ℝ)*(total D q Δ (SparseOuterLaw.law D c q hc hq).states[a.val] j:ℝ)-p j|) ≤
      γ*δ j+Real.sqrt ((g:ℝ)*(1+γ)*δ j) := by
  have hvar := SparseOuterLaw.deficit_variance D c q g hc hq j
  have he : (g:ℝ)^2*(targetMean D q j:ℝ)=(g:ℝ)*(1+γ)*δ j := by
    rw [pow_two,mul_assoc,hmean]
    ring
  rw [he] at hvar
  have hh := FiniteLaw.rescaling_noise (SparseOuterLaw.law D c q hc hq).realIndex
    (fun a => (deficit D q g (SparseOuterLaw.law D c q hc hq).states[a.val] j:ℝ))
    (hδ j) (hδhalf j) hγ (show (0:ℝ) ≤ g by exact_mod_cast hg.le)
    ((SparseOuterLaw.deficit_mean D c q g hc hq j).trans (hmean j)) hvar
  apply le_trans (le_of_eq ?_) hh
  apply FiniteLaw.expect_congr_support
  intro a _
  rw [total_deficit_identity D q Δ _ j hg heven hunit]
  congr 1
  linarith only [hp j]

end MetricKMedian.SparsePrepared
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseCoupledPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.SparsePrepared
open Finset SparseOuterLaw
open SparseSignedPreparation (State)
variable {n m f : ℕ}

theorem request_mean (D : Fin m → Finset (Fin n)) (a q : Fin m → ℚ) (Δ : ℕ)
    (ha : ∀ e, 0 ≤ a e ∧ a e ≤ 1) (hq : ∀ e, 0 ≤ q e) {g : ℝ} (hg : 0 ≤ g)
    (j : Fin n) (e : Fin m) :
    (SparseOuterLaw.law D a q ha hq).realIndex.expect (fun b =>
      g * (requests D q Δ (SparseOuterLaw.law D a q ha hq).states[b.val] j e : ℝ)) ≤
      if j ∈ D e then g * (q e : ℝ) else 0 := by
  calc
    _ ≤ (SparseOuterLaw.law D a q ha hq).realIndex.expect (fun b =>
        g * (activation D q (SparseOuterLaw.law D a q ha hq).states[b.val] e j : ℝ)) := by
      apply FiniteLaw.expect_mono
      intro b
      apply mul_le_mul_of_nonneg_left _ hg
      have h := requests_le D q Δ (SparseOuterLaw.law D a q ha hq).states[b.val] j e
      have he := activationCount_cast D q (SparseOuterLaw.law D a q ha hq).states[b.val] e j
      have hr : (requests D q Δ (SparseOuterLaw.law D a q ha hq).states[b.val] j e : ℚ) ≤
          activation D q (SparseOuterLaw.law D a q ha hq).states[b.val] e j := by
        rw [← he]
        exact_mod_cast h
      exact_mod_cast hr
    _ = _ := by
      rw [FiniteLaw.expect_mul, activation_real_mean]
      split_ifs <;> simp

end MetricKMedian.SparsePrepared
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_RestrictionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.Reduction.Enumeration
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open InstanceProgram (Raw view)
open MetricKMedian.MaskProgram
 theorem choicesRaw_choices {n : ℕ} (T : Finset (Fin n)) (c : ℕ) : choicesRaw c (setView T)=(choices T c).map setView :=
  choicesRaw_view T c

def arcpairs (T : Row) : List (ℕ × ℕ) :=
  (Preparation.RationalUnitInput.Program.ranks T).flatMap (fun i =>
    (Preparation.RationalUnitInput.Program.ranks T).map (fun j => (i,j)))
@[fun_prop] theorem arcpairs_poly : Poly arcpairs := by unfold arcpairs; apply list_flatMap; apply list_map <;> fun_prop; fun_prop
 theorem arcpairs_view {n : ℕ} (T : Finset (Fin n)) : arcpairs (setView T)=(pairs T).map (fun p => (p.1.val,p.2.val)) := by
  unfold arcpairs
  rw [Preparation.RationalUnitInput.Program.ranks_view]
  have hr : List.ofFn (fun a => (T.orderEmbOfFin rfl a).val)=(List.ofFn (T.orderEmbOfFin rfl)).map Fin.val := by simp only [List.map_ofFn,Function.comp_def]
  rw [hr]
  simp only [pairs,List.flatMap_map,List.map_flatMap,List.map_map,Function.comp_def]

def restrictData (x : Raw × (Row × List (ℕ × ℕ))) : Row :=
  (indices x.2.1).map (fun i => get x.2.1 i &&
    (x.2.2.map (fun p => decide ((x.1.2.2[p.1]?.getD [])[p.2]?.getD 0 ≤
      (x.1.2.2[p.1]?.getD [])[i]?.getD 0))).all id)
@[fun_prop] theorem restrictData_poly : Poly restrictData := by
  unfold restrictData
  have h : Poly (fun x : (Raw × (Row × List (ℕ × ℕ))) × ℕ =>
    (x.1.2.2.map (fun p => decide ((x.1.1.2.2[p.1]?.getD [])[p.2]?.getD 0 ≤
      (x.1.1.2.2[p.1]?.getD [])[x.2]?.getD 0))).all id) := by apply comp bool_all; apply list_map <;> fun_prop
  apply list_map <;> fun_prop

 theorem restrictData_view (I : Instance) (F : Finset (Fin I.n)) (ps : List (Fin I.n × Fin I.n)) :
    restrictData (view I,(setView F,ps.map (fun p => (p.1.val,p.2.val))))=setView (witnessedRestriction I F ps.toFinset) := by
  simp only [restrictData,view,indices,setView,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_def,MetricKMedian.MaskProgram.get,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta,Bool.and_eq_true,decide_eq_true_eq,
    witnessedRestriction,mem_filter,List.map_map,List.all_map,List.all_eq_true,id_eq,List.mem_toFinset]

def branchesData (a : ℕ) (x : Raw × Row) : Table :=
  (words a (arcpairs x.2)).map (fun ps => restrictData (x.1,(x.2,ps)))
@[fun_prop] theorem branchesData_poly (a : ℕ) : Poly (branchesData a) := by unfold branchesData; apply list_map <;> fun_prop
 theorem branchesData_view (I : Instance) (F : Finset (Fin I.n)) (a : ℕ) :
    branchesData a (view I,setView F)=(branches I F a).map setView := by
  simp only [branchesData,arcpairs_view,words_map,List.map_map,Function.comp_def,branches,restrictData_view]
end MetricKMedian.Reduction.Enumeration
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_DeletionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.Reduction.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open InstanceProgram (Raw view)
open MetricKMedian.MaskProgram
open Preparation.RationalNearest.MaskProgram (erase erase_view)
open Completion.Rational.BestProgram (card card_view)
open Enumeration

def eligibleData (x : (Raw × ℚ) × Row) : Row :=
  (indices x.2).map (fun i => get x.2 i && decide (costData (x.1.1,erase (i,x.2))-costData (x.1.1,x.2)≤x.1.2))
@[fun_prop] theorem eligibleData_poly : Poly eligibleData := by unfold eligibleData; apply list_map <;> fun_prop
def deleteData (x : (Raw × ℚ) × Row) : Row :=
  if x.1.1.2.1 < card x.2 then
    let E := eligibleData x
    if E.any id then erase (InstanceProgram.first E,x.2) else x.2
  else x.2
@[fun_prop] theorem deleteData_poly : Poly deleteData := by unfold deleteData; fun_prop

def historyData : ℕ → (Raw × ℚ) × Row → Row
  | 0,x => x.2
  | c+1,x => deleteData (x.1,historyData c x)
@[fun_prop] theorem historyData_poly (c : ℕ) : Poly (historyData c) := by
  induction c with
  | zero => exact snd
  | succ c ih => change Poly (fun x => deleteData (x.1,historyData c x)); fun_prop
end MetricKMedian.Reduction.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_LocalCompletionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Reduction.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open InstanceProgram (Raw view)
open MetricKMedian.MaskProgram
open Preparation.RationalNearest.MaskProgram (erase erase_view insert insert_view)
open Enumeration

def getDist (x : Raw × (ℕ × ℕ)) : ℚ := (x.1.2.2[x.2.1]?.getD [])[x.2.2]?.getD 0
@[fun_prop] theorem getDist_poly : Poly getDist := by unfold getDist; fun_prop

def radiiData (x : Raw × Row) : List ℚ := (indices x.2).map (fun t => nearestData (x.1.2.2[t]?.getD [],erase (t,x.2)))
@[fun_prop] theorem radiiData_poly : Poly radiiData := by unfold radiiData; apply list_map <;> fun_prop

abbrev LocalRaw := (Raw × (Row × Row)) × (List ℚ × ℚ)
def candidatesData (x : LocalRaw × ℕ) : Row :=
  (indices x.1.1.2.1).map (fun a => get x.1.1.2.1 a &&
    decide (getDist (x.1.1.1,(x.2,a))≤x.1.2.2*(x.1.2.1[x.2]?.getD 0)))
@[fun_prop] theorem candidatesData_poly : Poly candidatesData := by unfold candidatesData; apply list_map <;> fun_prop

def weightData (x : LocalRaw × (ℕ × ℕ)) : ℚ :=
  ((indices x.1.1.1.1.1).map (fun j => if get x.1.1.1.1.1 j &&
    decide (3*getDist (x.1.1.1,(j,x.2.1))≤x.1.2.1[x.2.1]?.getD 0) then
      nearestData (x.1.1.1.2.2[j]?.getD [],insert (x.2.2,x.1.1.2.2)) else 0)).sum
@[fun_prop] theorem weightData_poly : Poly weightData := by unfold weightData; apply comp rat_sum; apply list_map <;> fun_prop

def pickData (x : List ℚ × Row) : Row :=
  if x.2.any id then InstanceProgram.singletonRaw (x.2,MetricKMedian.MaskProgram.nearest x) else x.2.map (fun _ => false)
@[fun_prop] theorem pickData_poly : Poly pickData := by unfold pickData; fun_prop

def localData (x : LocalRaw × ℕ) : Row :=
  pickData ((indices x.1.1.2.1).map (fun a => weightData (x.1,(x.2,a))),candidatesData x)
@[fun_prop] theorem localData_poly : Poly localData := by unfold localData; apply comp pickData_poly; apply pair; apply list_map <;> fun_prop; fun_prop

def unionData (x : Row × Table) : Row := (indices x.1).map (fun i => (x.2.map (fun S => get S i)).any id)
@[fun_prop] theorem unionData_poly : Poly unionData := by unfold unionData; apply list_map; apply comp bool_any; apply list_map <;> fun_prop; fun_prop

def completionData (x : LocalRaw × Row) : Row := union (x.1.1.2.2,unionData (x.2,
  (Preparation.RationalUnitInput.Program.ranks x.2).map (fun t => localData (x.1,t))))
@[fun_prop] theorem completionData_poly : Poly completionData := by
  unfold completionData
  have hm : Poly (fun x : LocalRaw × Row => (Preparation.RationalUnitInput.Program.ranks x.2).map (fun t => localData (x.1,t))) := by apply list_map <;> fun_prop
  fun_prop
end MetricKMedian.Reduction.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_BranchProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.Reduction.Program
open Finset Preparation Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView)
open InstanceProgram (Raw view)
open Completion.Rational.BestProgram (card card_view)
open Enumeration
variable (r : ℕ) (hr : 0 < r) {η τ : ℝ} (p : RationalAllParameters η τ) (c a b : ℕ) (δ : ℚ)
def branchOut (B : Branch) : List (Finset (Fin B.original.n)) :=
  if h : B.allowed then outcomes B.original B.facilities ((B.restricted h).computedPseudo r hr p c) δ c b else []
end MetricKMedian.Reduction.Program
end

end OAI
end


