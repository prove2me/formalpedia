-- Prove2me | Definitions.Def_OAIQ053K003
-- name    : OAIQ053K003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T05:53:24.704994+00:00
-- url     : https://prove2.me/theorems/c865cc83-917f-4b5e-b878-2e49280a0933
-- title:
--   Definitions bundle OAIQ053K003 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 125 declarations of OpenAI's Lean: 73 definitions, 6 inductive types or structures, 1 instance and 45 theorems. The definitions and types are `OAI.MetricKMedian.Complexity.FiniteComposition.Compose.Alphabet`, `OAI.MetricKMedian.Complexity.FiniteComposition.Compose.Key`, `OAI.MetricKMedian.Complexity.FiniteComposition.Compose.Label`, `OAI.MetricKMedian.Complexity.FiniteComposition.Compose.State`, `OAI.MetricKMedian.Complexity.FiniteComposition.Compose.auxiliary`, `OAI.MetricKMedian.Complexity.FiniteComposition.Compose.boundaryCfg`, `OAI.MetricKMedian.Complexity.FiniteComposition.Compose.clean`, `OAI.MetricKMedian.Complexity.FiniteComposition.Compose.code`, `OAI.MetricKMedian.Complexity.FiniteComposition.Compose.following`, `OAI.MetricKMedian.Complexity.FiniteComposition.Compose.left`, `OAI.MetricKMedian.Complexity.FiniteComposition.Compose.machine`, `OAI.MetricKMedian.Complexity.FiniteComposition.Compose.phaseLabel`, `OAI.MetricKMedian.Complexity.FiniteComposition.Compose.right`, `OAI.MetricKMedian.Complexity.FiniteComposition.Compose.source`, `OAI.MetricKMedian.Complexity.FiniteComposition.Compose.sourceAlphabet`, `OAI.MetricKMedian.Complexity.FiniteComposition.Compose.target`, `OAI.MetricKMedian.Complexity.FiniteComposition.Compose.targetAlphabet`, `OAI.MetricKMedian.Complexity.FiniteComposition.Compose.transfer`, `OAI.MetricKMedian.Complexity.FiniteComposition.Compose.transferCfg`, `OAI.MetricKMedian.Complexity.FiniteComposition.Embedding`, `OAI.MetricKMedian.Complexity.FiniteComposition.Embedding.cfg`, `OAI.MetricKMedian.Complexity.FiniteComposition.Embedding.stmt`, `OAI.MetricKMedian.Complexity.FiniteComposition.Machine`, `OAI.MetricKMedian.Complexity.FiniteComposition.Machine.Cfg`, `OAI.MetricKMedian.Complexity.FiniteComposition.Machine.finalCfg`, `OAI.MetricKMedian.Complexity.FiniteComposition.Machine.growth`, `OAI.MetricKMedian.Complexity.FiniteComposition.Machine.initialCfg`, `OAI.MetricKMedian.Complexity.FiniteComposition.Machine.pushes`, `OAI.MetricKMedian.Complexity.FiniteComposition.Machine.single`, `OAI.MetricKMedian.Complexity.FiniteComposition.Machine.step`, `OAI.MetricKMedian.Complexity.FiniteComposition.Machine.tm`, `OAI.MetricKMedian.Complexity.FiniteComposition.twoStacks`, `OAI.MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram.Raw`, `OAI.MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram.Raw`, `OAI.MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram.cap`, `OAI.MetricKMedian.FixedBatch.RationalParameters.candidateGood`, `OAI.MetricKMedian.FixedBatch.batchConstant`, `OAI.MetricKMedian.FractionalDual.affine`, `OAI.MetricKMedian.FractionalDual.thresholds`, `OAI.MetricKMedian.FractionalDual.value` and 39 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Binary_NumericParserProgram`, `KMedian_Compression_GaussianListOperations`, `KMedian_Geometry_RationalFractionalInput`, `KMedian_Geometry_RationalIntervals`, `KMedian_Geometry_RationalSplitEnumeration`, `KMedian_Geometry_RationalSplitInput`, `KMedian_Geometry_RationalSplitting`, `KMedian_Geometry_RationalUnitInput`, `KMedian_Hardness_Composition`, `KMedian_Optimization_ApproximateFractional`, `KMedian_Optimization_ApproximateLPSelection`, `KMedian_Optimization_ComputedNearest`, `KMedian_Optimization_FractionalDual`, `KMedian_Optimization_FractionalInputProgram`, `KMedian_Preparation_PreparationParameters`, `KMedian_Preparation_PreparedScanProgram`, `KMedian_Preparation_RationalPreparedScan`, `KMedian_Preparation_RationalSupplierPreparation`, `KMedian_Preparation_SupplierListOperations`, `KMedian_Process_BatchUniform`, `KMedian_Process_RoundCountsProgram`, `KMedian_Programs_InstanceDataProgram`, `KMedian_Programs_MaximumProgram`, `KMedian_Programs_NearestListProgram`, `KMedian_Programs_OriginalMaskProgram`, `KMedian_Programs_RationalSortProgram`, `KMedian_Programs_SplitListProgram`, `KMedian_Programs_UnitGeometryProgram`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K015`, `OAIQ053K017`, `OAIQ053K018`, `OAIQ053K019`, `OAIQ053K020`, `OAIQ053K021` and `OAIQ053K022`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_NumericParserProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.InputParser
def width (xs : List Bool) : ℕ := xs.findIdx Bool.not
end MetricKMedian.InputParser
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Gaussian.ListOperation
open Finset
universe uα uβ
variable {α : Type uα} {β : Type uβ}

 theorem zip_ofFn {n : ℕ} (f : Fin n → α) (g : Fin n → β) :
    (List.ofFn f).zip (List.ofFn g)=List.ofFn (fun i => (f i,g i)) := by
  apply List.ext_getElem (by simp only [List.length_zip,List.length_ofFn,min_self])
  intro i hi hj
  simp only [List.getElem_zip,List.getElem_ofFn]

end MetricKMedian.Gaussian.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
namespace RationalIntervals

def height (Q : Finset ℚ) : ℚ := (insert 0 Q).max' (insert_nonempty _ _)
def previous (Q : Finset ℚ) (q : ℚ) : ℚ := height (Q.filter (fun p => p<q))
def length (Q : Finset ℚ) (q : ℚ) : ℚ := q-previous Q q

theorem height_nonneg (Q : Finset ℚ) : 0 ≤ height Q :=
  le_max' _ _ (mem_insert_self _ _)

theorem height_eq (Q : Finset ℚ) (q : ℚ) (hq : q ∈ Q) (hq0 : 0 ≤ q)
    (hmax : ∀ p ∈ Q, p ≤ q) : height Q=q := by
  apply le_antisymm
  · apply max'_le
    intro p hp
    rcases mem_insert.mp hp with rfl | hp
    · exact hq0
    · exact hmax p hp
  · exact le_max' _ _ (mem_insert_of_mem hq)

theorem previous_lt (Q : Finset ℚ) {q : ℚ} (hq : 0 < q) : previous Q q < q := by
  have hm := max'_mem (insert 0 (Q.filter (fun p => p<q))) (insert_nonempty _ _)
  rcases mem_insert.mp hm with he | hm
  · rw [show previous Q q=0 from he]; exact hq
  · exact (mem_filter.mp hm).2

theorem length_pos (Q : Finset ℚ) {q : ℚ} (hq : 0 < q) : 0 < length Q q :=
  sub_pos.mpr (previous_lt Q hq)

theorem length_le (Q : Finset ℚ) (q : ℚ) : length Q q ≤ q :=
  sub_le_self _ (height_nonneg _)

theorem previous_erase_max (Q : Finset ℚ) {a q : ℚ} (hqa : q ≤ a) :
    previous (Q.erase a) q=previous Q q := by
  unfold previous
  congr 1
  ext p
  simp only [mem_filter,mem_erase]
  constructor
  · rintro ⟨⟨_,hp⟩,hpq⟩; exact ⟨hp,hpq⟩
  · rintro ⟨hp,hpq⟩
    exact ⟨⟨ne_of_lt (hpq.trans_le hqa),hp⟩,hpq⟩

theorem sum_lengths (Q : Finset ℚ) (hQ : ∀ q ∈ Q, 0 < q) :
    (∑ q ∈ Q, length Q q)=height Q := by
  revert hQ
  refine Q.strongInductionOn ?_
  intro Q ih hQ
  by_cases hne : Q.Nonempty
  · let a := Q.max' hne
    have ha : a ∈ Q := max'_mem Q hne
    have hamax : ∀ q ∈ Q, q ≤ a := fun q hq => le_max' Q q hq
    have hheight : height Q=a := height_eq Q a ha (hQ a ha).le hamax
    have hprev : previous Q a=height (Q.erase a) := by
      unfold previous
      congr 1
      ext q
      simp only [mem_filter,mem_erase]
      constructor
      · rintro ⟨hq,hqa⟩; exact ⟨ne_of_lt hqa,hq⟩
      · rintro ⟨hne,hq⟩; exact ⟨hq,lt_of_le_of_ne (hamax q hq) hne⟩
    have hsum := ih (Q.erase a) (erase_ssubset ha) (fun q hq => hQ q (mem_of_mem_erase hq))
    have hold : ∀ q ∈ Q.erase a, length Q q=length (Q.erase a) q := by
      intro q hq
      rw [length,length,previous_erase_max Q (hamax q (mem_of_mem_erase hq))]
    rw [← sum_erase_add Q (length Q) ha,sum_congr rfl hold,hsum,length,hprev,hheight]
    ring
  · have he := not_nonempty_iff_eq_empty.mp hne
    subst Q
    simp [height]

theorem previous_filter_le (Q : Finset ℚ) {b q : ℚ} (hqb : q ≤ b) :
    previous (Q.filter (fun p => p ≤ b)) q=previous Q q := by
  unfold previous
  congr 1
  ext p
  simp only [mem_filter]
  exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,(h.2.trans_le hqb).le⟩,h.2⟩⟩

theorem prefix_sum (Q : Finset ℚ) (hQ : ∀ q ∈ Q, 0 < q) {b : ℚ}
    (hb : b=0 ∨ b ∈ Q) :
    (∑ q ∈ Q.filter (fun p => p ≤ b), length Q q)=b := by
  rcases hb with rfl | hb
  · have he : Q.filter (fun p => p ≤ 0)=∅ := by
      apply filter_eq_empty_iff.mpr
      intro q hq hq0
      exact not_le_of_gt (hQ q hq) hq0
    rw [he,sum_empty]
  · calc
      _ = ∑ q ∈ Q.filter (fun p => p ≤ b), length (Q.filter (fun p => p ≤ b)) q := by
        apply sum_congr rfl
        intro q hq
        rw [length,length,previous_filter_le Q (mem_filter.mp hq).2]
      _ = height (Q.filter (fun p => p ≤ b)) :=
        sum_lengths _ (fun q hq => hQ q (mem_filter.mp hq).1)
      _ = b := height_eq _ b (mem_filter.mpr ⟨hb,le_rfl⟩) (hQ b hb).le
        (fun q hq => (mem_filter.mp hq).2)

end RationalIntervals
end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalSplitting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation.RationalSplitting
open Finset RationalIntervals
variable {I J : Type} [Fintype I] [Fintype J]

def cuts (y : I → ℚ) (x : J → I → ℚ) (i : I) : Finset ℚ :=
  (insert (y i) (univ.image (fun j => x j i))).filter (fun q => 0 < q)

abbrev Piece (y : I → ℚ) (x : J → I → ℚ) := Σ i, ↥(cuts y x i)

def weight (y : I → ℚ) (x : J → I → ℚ) (a : Piece y x) : ℚ :=
  length (cuts y x a.1) a.2.val

def assignment (y : I → ℚ) (x : J → I → ℚ) (j : J) : Finset (Piece y x) :=
  univ.filter (fun a => a.2.val ≤ x j a.1)

omit [Fintype I] in
theorem cuts_pos (y : I → ℚ) (x : J → I → ℚ) (i : I) :
    ∀ q ∈ cuts y x i, 0 < q := fun _ h => (mem_filter.mp h).2

omit [Fintype I] in
theorem cuts_le (y : I → ℚ) (x : J → I → ℚ) (hx : ∀ j i, x j i ≤ y i)
    (i : I) : ∀ q ∈ cuts y x i, q ≤ y i := by
  intro q hq
  rcases mem_insert.mp (mem_filter.mp hq).1 with rfl | hq
  · exact le_rfl
  · obtain ⟨j,_,rfl⟩ := mem_image.mp hq
    exact hx j i

omit [Fintype I] in
theorem weight_pos (y : I → ℚ) (x : J → I → ℚ) (a : Piece y x) : 0 < weight y x a :=
  length_pos _ (cuts_pos y x a.1 _ a.2.property)

omit [Fintype I] in
theorem weight_le (y : I → ℚ) (x : J → I → ℚ) (hx : ∀ j i, x j i ≤ y i)
    (a : Piece y x) : weight y x a ≤ y a.1 :=
  (length_le _ _).trans (cuts_le y x hx a.1 _ a.2.property)

omit [Fintype I] in
theorem assigned_fiber (y : I → ℚ) (x : J → I → ℚ) (hx0 : ∀ j i, 0 ≤ x j i)
    (j : J) (i : I) :
    (∑ q : ↥(cuts y x i), if q.val ≤ x j i then length (cuts y x i) q.val else 0)=x j i := by
  change (∑ q : ↥(cuts y x i), (fun q : ℚ => if q ≤ x j i then length (cuts y x i) q else 0) q.val)=x j i
  rw [sum_coe_sort (cuts y x i) (fun q : ℚ => if q ≤ x j i then length (cuts y x i) q else 0),← sum_filter]
  apply prefix_sum _ (cuts_pos y x i)
  by_cases hz : x j i=0
  · exact Or.inl hz
  · exact Or.inr (mem_filter.mpr ⟨mem_insert_of_mem (mem_image.mpr ⟨j,mem_univ _,rfl⟩),
      lt_of_le_of_ne (hx0 j i) (Ne.symm hz)⟩)

theorem sum_assignment (y : I → ℚ) (x : J → I → ℚ) (hx0 : ∀ j i, 0 ≤ x j i)
    (j : J) : (∑ a ∈ assignment y x j, weight y x a)=∑ i, x j i := by
  rw [assignment,sum_filter,Fintype.sum_sigma]
  exact sum_congr rfl (fun i _ => assigned_fiber y x hx0 j i)

theorem nearest_assignment (y : I → ℚ) (x : J → I → ℚ) (hx : ∀ j i, x j i ≤ y i)
    (d : J → I → ℝ)
    (horder : ∀ j i b, 0 < x j i → x j b < y b → d j i ≤ d j b)
    (j : J) (a : Piece y x) (ha : a ∈ assignment y x j)
    (b : Piece y x) (hb : b ∉ assignment y x j) : d j a.1 ≤ d j b.1 := by
  have ha' : a.2.val ≤ x j a.1 := (mem_filter.mp ha).2
  have hb' : x j b.1 < b.2.val := lt_of_not_ge (fun h => hb (mem_filter.mpr ⟨mem_univ _,h⟩))
  exact horder j a.1 b.1 ((cuts_pos y x a.1 _ a.2.property).trans_le ha')
    (hb'.trans_le (cuts_le y x hx b.1 _ b.2.property))

end MetricKMedian.Preparation.RationalSplitting
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalSplitEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.Preparation.RationalSplitting
open Finset RationalIntervals
variable {f j : ℕ}

def count (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ) := ∑ i, (cuts y x i).card

def index (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ) :
    Fin (count y x) ≃ Piece y x :=
  finSigmaFinEquiv.symm.trans (Equiv.sigmaCongrRight (fun i => (cuts y x i).orderIsoOfFin rfl |>.toEquiv))

def weights (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ) (a : Fin (count y x)) : ℚ :=
  weight y x (index y x a)

def original (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ) (a : Fin (count y x)) : Fin f :=
  (index y x a).1

def assigned (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ) (c : Fin j) : Finset (Fin (count y x)) :=
  (assignment y x c).map (index y x).symm.toEmbedding

theorem mem_assigned (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ)
    (c : Fin j) (a : Fin (count y x)) : a∈assigned y x c ↔ index y x a∈assignment y x c := by
  simp only [assigned,mem_map,Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨b,hb,hba⟩
    rw [← hba,(index y x).apply_symm_apply]
    exact hb
  · intro ha
    exact ⟨index y x a,ha,(index y x).symm_apply_apply a⟩

theorem assigned_sum {K : Type} [AddCommMonoid K]
    (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ) (c : Fin j) (v : Piece y x → K) :
    (∑ a ∈ assigned y x c, v (index y x a))=∑ a ∈ assignment y x c, v a := by
  rw [assigned,sum_map]
  simp only [Equiv.toEmbedding_apply,Equiv.apply_symm_apply]

end MetricKMedian.Preparation.RationalSplitting
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_FractionalDual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FractionalDual
open Finset
variable {ι : Type} [Fintype ι]

def affine (d y : ι → ℚ) (τ : ℚ) : ℚ := τ-∑ i, y i*max 0 (τ-d i)

theorem weak_duality (d y x : ι → ℚ) (τ : ℚ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ y i) (hxs : ∑ i, x i=1) :
    affine d y τ ≤ ∑ i, x i*d i := by
  have ht : ∀ i, τ*x i-y i*max 0 (τ-d i) ≤ x i*d i := by
    intro i
    by_cases hi : τ ≤ d i
    · rw [max_eq_left (sub_nonpos.mpr hi),mul_zero,sub_zero,mul_comm τ]
      exact mul_le_mul_of_nonneg_left hi (hx i).1
    · rw [max_eq_right (sub_nonneg.mpr (le_of_not_ge hi))]
      have hh := mul_le_mul_of_nonneg_right (hx i).2 (sub_nonneg.mpr (le_of_not_ge hi))
      linarith
  have hs := sum_le_sum (fun i (_ : i ∈ univ) => ht i)
  simpa only [sum_sub_distrib,← mul_sum,hxs,mul_one,affine] using hs

theorem ordered_attains [DecidableEq ι] (d y x : ι → ℚ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ y i) (hxs : ∑ i, x i=1)
    (ho : ∀ i a, 0 < x i → x a < y a → d i ≤ d a) :
    ∃ a, affine d y (d a)=∑ i, x i*d i := by
  let U := univ.filter (fun i => 0 < x i)
  have hU : U.Nonempty := by
    by_contra hn
    have hz : ∀ i, x i=0 := fun i => le_antisymm
      (le_of_not_gt (fun hp => hn ⟨i,mem_filter.mpr ⟨mem_univ _,hp⟩⟩)) (hx i).1
    simp only [hz,sum_const_zero] at hxs
    norm_num at hxs
  obtain ⟨a,ha,hmax⟩ := U.exists_max_image d hU
  refine ⟨a,?_⟩
  have hapos := (mem_filter.mp ha).2
  have hi : ∀ i, y i*max 0 (d a-d i)=x i*(d a-d i) := by
    intro i
    by_cases hl : d i < d a
    · have he : x i=y i := by
        apply le_antisymm (hx i).2
        exact le_of_not_gt (fun hlt => (not_le_of_gt hl) (ho a i hapos hlt))
      rw [he,max_eq_right (sub_nonneg.mpr hl.le)]
    · by_cases he : d i=d a
      · rw [he,sub_self,max_self,mul_zero,mul_zero]
      · have hlt : d a < d i := lt_of_le_of_ne (le_of_not_gt hl) (Ne.symm he)
        have hz : x i=0 := by
          apply le_antisymm _ (hx i).1
          exact le_of_not_gt (fun hp => (not_le_of_gt hlt)
            (hmax i (mem_filter.mpr ⟨mem_univ _,hp⟩)))
        rw [hz,zero_mul,max_eq_left (sub_nonpos.mpr hlt.le),mul_zero]
  unfold affine
  simp_rw [hi,mul_sub]
  rw [sum_sub_distrib,← sum_mul,hxs,one_mul]
  ring

def thresholds (d : ι → ℚ) (H : ℚ) : Finset ℚ := insert 0 (insert H (univ.image d))

def value (d y : ι → ℚ) (H : ℚ) : ℚ :=
  ((thresholds d H).image (affine d y)).max'
    ((insert_nonempty 0 _).image _)

theorem affine_le_value (d y : ι → ℚ) (H τ : ℚ) (hτ : τ ∈ thresholds d H) :
    affine d y τ ≤ value d y H :=
  le_max' _ _ (mem_image.mpr ⟨τ,hτ,rfl⟩)

theorem value_le_assignment (d y x : ι → ℚ) (H : ℚ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ y i) (hxs : ∑ i, x i=1) :
    value d y H ≤ ∑ i, x i*d i := by
  apply max'_le
  intro q hq
  obtain ⟨τ,_,rfl⟩ := mem_image.mp hq
  exact weak_duality d y x τ hx hxs

end MetricKMedian.FractionalDual
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_ComputedNearest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {n : ℕ}

structure Filling (U : Finset (Fin n)) (y d : Fin n → ℚ) (t : ℚ) where
  amount : Fin n → ℚ
  outside : ∀ i, i ∉ U → amount i=0
  bounds : ∀ i ∈ U, 0 ≤ amount i ∧ amount i ≤ y i
  total : ∑ i ∈ U, amount i=t
  ordered : ∀ i ∈ U, ∀ a ∈ U, 0 < amount i → amount a < y a → d i ≤ d a

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalUnitInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.Preparation
open Finset

structure RationalUnitInput (f j : ℕ) where
  y : Fin f → ℚ
  F : Fin j → Finset (Fin f)
  dc : Fin j → Fin f → ℚ
  dd : Fin j → Fin j → ℚ
  df : Fin f → Fin f → ℚ
  hy : ∀ a, 0<y a
  hy1 : ∀ a, y a≤1
  hu : ∀ c, ∑ a ∈ F c, y a=1
  hdc : ∀ c a, 0≤dc c a
  hdd : ∀ c, dd c c=0
  hsymm : ∀ c c', dd c c'=dd c' c
  hnear : ∀ c, ∀ a ∈ F c, ∀ b ∉ F c, dc c a≤dc c b

end MetricKMedian.Preparation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalSplitInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.Preparation.RationalSplitting
open Finset
variable {f j : ℕ}

 theorem nearest_rational (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ)
    (hx1 : ∀ c i, x c i≤y i) (dc : Fin j → Fin f → ℚ)
    (horder : ∀ c a b, 0<x c a → x c b<y b → dc c a≤dc c b)
    (c : Fin j) (a : Fin (count y x)) (ha : a∈assigned y x c)
    (b : Fin (count y x)) (hb : b∉assigned y x c) :
    dc c (original y x a)≤dc c (original y x b) := by
  have hh := nearest_assignment y x hx1 (fun c a => (dc c a:ℝ))
    (fun c a b ha hb => by exact_mod_cast horder c a b ha hb)
    c (index y x a) ((mem_assigned y x c a).mp ha) (index y x b)
    (fun hh => hb ((mem_assigned y x c b).mpr hh))
  exact_mod_cast hh

def input (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ)
    (dc : Fin j → Fin f → ℚ) (dd : Fin j → Fin j → ℚ) (df : Fin f → Fin f → ℚ)
    (_ : ∀ i, 0≤y i) (hy1 : ∀ i, y i≤1)
    (hx0 : ∀ c i, 0≤x c i) (hx1 : ∀ c i, x c i≤y i) (hxu : ∀ c, ∑ i, x c i=1)
    (hdc : ∀ c a, 0≤dc c a) (hdd : ∀ c, dd c c=0) (hds : ∀ c c', dd c c'=dd c' c)
    (horder : ∀ c a b, 0<x c a → x c b<y b → dc c a≤dc c b) : RationalUnitInput (count y x) j where
  y := weights y x
  F := assigned y x
  dc := fun c a => dc c (original y x a)
  dd := dd
  df := fun a b => df (original y x a) (original y x b)
  hy := fun a => weight_pos y x (index y x a)
  hy1 := fun a => (weight_le y x hx1 (index y x a)).trans (hy1 (original y x a))
  hu := fun c => (assigned_sum y x c (weight y x)).trans ((sum_assignment y x hx0 c).trans (hxu c))
  hdc := fun c a => hdc c (original y x a)
  hdd := hdd
  hsymm := hds
  hnear := nearest_rational y x hx1 dc horder

end MetricKMedian.Preparation.RationalSplitting
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_ApproximateFractional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.TruncatedLP
open Finset
variable {n m : ℕ} [NeZero n] [NeZero m]

structure FractionalData (n m : ℕ) where
  opening : Vector ℚ n
  assignment : Vector (Vector ℚ n) m

end MetricKMedian.TruncatedLP
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_ApproximateLPSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.TruncatedLP
open Finset
variable {n m : ℕ} [NeZero n] [NeZero m]

def FractionalData.Valid (out : FractionalData n m) (k : ℕ) : Prop :=
    (∀ i : Fin n, 0 ≤ out.opening[i.val] ∧ out.opening[i.val] ≤ 1) ∧
    (∀ (j : Fin m) (i : Fin n), 0 ≤ out.assignment[j.val][i.val] ∧
      out.assignment[j.val][i.val] ≤ out.opening[i.val]) ∧
    (∀ j : Fin m, ∑ i : Fin n, out.assignment[j.val][i.val]=1) ∧
    (∑ i : Fin n, out.opening[i.val]) ≤ (k:ℚ)+1

def FractionalData.value (out : FractionalData n m) (d : Fin m → Fin n → ℚ) : ℚ :=
  ∑ j : Fin m, ∑ i : Fin n, out.assignment[j.val][i.val]*d j i

end MetricKMedian.TruncatedLP
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalFractionalInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.Preparation
open Finset
variable {f j : ℕ}

namespace FractionalRefinement

variable (a : TruncatedLP.FractionalData f j) (k : ℕ) (ha : a.Valid k) (hj : 0<j)

def y (i : Fin f) : ℚ := a.opening[i.val]

include ha hj in
theorem mass_one : 1≤∑ i, y a i := by
  let c : Fin j := ⟨0,hj⟩
  calc
    1 = ∑ i : Fin f, a.assignment[c.val][i.val] := (ha.2.2.1 c).symm
    _ ≤ ∑ i, y a i := sum_le_sum (fun i _ => (ha.2.1 c i).2)

end FractionalRefinement
end MetricKMedian.Preparation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_PreparationParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation

noncomputable def farFactor (δ p₀ α β γ : ℝ) : ℝ :=
  max (1/p₀) (1+2*δ/(1-β-δ))*((1+α)/(1-α))+(β+1+δ)*γ/δ
noncomputable def failureFactor (γ g : ℝ) : ℝ := 4*g*(1+γ)/γ

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_BatchUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset

noncomputable def batchConstant (Δ : ℕ) : ℝ :=
  let n : ℝ := Δ^2+Δ
  16*n*(Δ:ℝ)^2+256*n^2+16*n+6

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_RationalPreparedScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.FixedBatch.RationalParameters
open Finset
variable {τ : ℝ}
variable {F H X : Type} [LinearOrder F] [Fintype F] [DecidableEq H]
  [PseudoMetricSpace X] {j : ℕ}

def candidateGood (B : ℚ) (O : Finset H) : Bool := decide (O.Nonempty ∧ (O.card:ℚ) ≤ B)

end MetricKMedian.FixedBatch.RationalParameters
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_RationalSupplierPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                   
section
namespace MetricKMedian.Preparation.RationalSuppliers
open Finset
variable {f n : ℕ}

abbrev size (f n : ℕ) := f+(n*n+n)

end MetricKMedian.Preparation.RationalSuppliers
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_NearestListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Function Finset

namespace Nearest
abbrev Entry := ℕ × (ℚ × ℚ)

def before (a b : Entry) : Bool := decide (a.2.2 < b.2.2 ∨ a.2.2=b.2.2 ∧ a.1 < b.1)
def prior (es : List Entry) (a : Entry) : ℚ := ((es.filter (fun b => before b a)).map (fun e => e.2.1)).sum
def amount (es : List Entry) (a : Entry) : ℚ := min a.2.1 (max 0 (1-prior es a))
end Nearest
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_OriginalMaskProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.MaskProgram
open Finset

def pullback (x : List ℚ × List ℕ) : List ℚ := x.2.map (fun i => x.1[i]?.getD 0)
end MetricKMedian.MaskProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_MaximumProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.MaskProgram
open Finset
def maximum (xs : List ℚ) : ℚ := xs.foldl max (xs.head?.getD 0)
end MetricKMedian.MaskProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_SupplierListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Preparation.RationalSuppliers.Program
open Finset
abbrev QRow := List ℚ
abbrev BTable := List (List Bool)
abbrev SupplierRaw := QRow × (BTable × (BTable × (QRow × (QRow × ℚ))))
end MetricKMedian.Preparation.RationalSuppliers.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_RationalSortProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.RationalSortProgram
open Finset

def insertData (x : List ℚ × ℚ) : List ℚ :=
  x.1.filter (fun a => decide (a<x.2)) ++ x.2::x.1.filter (fun a => decide (x.2<a))
end MetricKMedian.RationalSortProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_SplitListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.Preparation.RationalSplitting.Program
open Finset
open MetricKMedian.MaskProgram
abbrev Raw := List ℚ × List (List ℚ)
end MetricKMedian.Preparation.RationalSplitting.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_FractionalInputProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Preparation.FractionalRefinement.Program
open Finset
open MetricKMedian.MaskProgram
abbrev Matrix := List (List ℚ)
abbrev Raw := List ℚ × (Matrix × (Matrix × Matrix))
structure Input where
  f : ℕ
  j : ℕ
  k : ℕ
  a : TruncatedLP.FractionalData f j
  ha : a.Valid k
  hj : 0<j
  dc : Fin j → Fin f → ℚ
  dd : Fin j → Fin j → ℚ
  df : Fin f → Fin f → ℚ
  hdc : ∀ c i, 0≤dc c i
  hdd : ∀ c, dd c c=0
  hds : ∀ c c', dd c c'=dd c' c
end MetricKMedian.Preparation.FractionalRefinement.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_UnitGeometryProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.Preparation.RationalUnitInput.Program
open Finset
open MetricKMedian.MaskProgram

def pickRows {α : Type} [Inhabited α] (x : List (List α) × List ℕ) : List (List α) :=
  x.2.map (fun i => x.1[i]?.getD [])
end MetricKMedian.Preparation.RationalUnitInput.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_InstanceDataProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.InstanceProgram
open Finset Preparation
open MaskProgram
abbrev Matrix := List (List ℚ)
end MetricKMedian.InstanceProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_RoundCountsProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram
open Finset
variable {τ : ℝ}
abbrev Raw := List Unit × ((List (List ℚ) × List (List ℚ)) × List ℕ)

def cap (Δ : ℕ) (ns : List ℕ) : Bool := (ns.map (fun n => decide (n≤Δ))).all id
end MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_PreparedScanProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram
open Finset
variable {τ : ℝ}
abbrev Raw := (List Unit × List ℕ) × ((List (List ℚ) × List (List ℚ)) × (List (List ℕ) × ℚ))
end MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Composition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Complexity.FiniteComposition
open Turing Function Finset Polynomial

structure Machine where
  K : Type
  [decK : DecidableEq K]
  [finK : Fintype K]
  Γ : K → Type
  [finΓ : ∀ k, Fintype (Γ k)]
  input : K
  output : K
  inputAlphabet : Γ input ≃ Bool
  outputAlphabet : Γ output ≃ Bool
  Label : Type
  [finLabel : Fintype Label]
  main : Label
  State : Type
  [finState : Fintype State]
  initial : State
  code : Label → TM2.Stmt Γ Label State

attribute [instance] Machine.decK Machine.finK Machine.finΓ Machine.finLabel Machine.finState

theorem cfg_ext {K L S : Type} {Γ : K → Type} {a b : TM2.Cfg Γ L S}
    (hl : a.l = b.l) (hv : a.var = b.var) (hs : a.stk = b.stk) : a = b := by
  cases a
  cases b
  cases hl
  cases hv
  cases hs
  rfl

namespace Machine

def tm (M : Machine) : FinTM2 where
  K := M.K
  k₀ := M.input
  k₁ := M.output
  Γ := M.Γ
  Λ := M.Label
  main := M.main
  σ := M.State
  initialState := M.initial
  m := M.code

abbrev Cfg (M : Machine) := TM2.Cfg M.Γ M.Label M.State
abbrev step (M : Machine) : M.Cfg → Option M.Cfg := TM2.step M.code

def single {K : Type} [DecidableEq K] {Γ : K → Type}
    (k : K) (xs : List (Γ k)) : ∀ j, List (Γ j) := update (fun _ => []) k xs

def initialCfg (M : Machine) (xs : List Bool) : M.Cfg :=
  ⟨some M.main, M.initial, single M.input (xs.map M.inputAlphabet.symm)⟩

def finalCfg (M : Machine) (xs : List Bool) : M.Cfg :=
  ⟨none, M.initial, single M.output (xs.map M.outputAlphabet.symm)⟩

@[simp] theorem init_eq (M : Machine) (xs : List Bool) :
    initList M.tm (xs.map M.inputAlphabet.symm) = M.initialCfg xs := by
  dsimp only [tm]
  apply cfg_ext <;> try rfl
  funext k
  by_cases h : k = M.input
  · subst k; simp [initList, initialCfg, single]
  · change (dite (k = M.input) _ _) = update (fun _ => []) M.input _ k
    simp [h]

@[simp] theorem halt_eq (M : Machine) (xs : List Bool) :
    haltList M.tm (xs.map M.outputAlphabet.symm) = M.finalCfg xs := by
  dsimp only [tm]
  apply cfg_ext <;> try rfl
  funext k
  by_cases h : k = M.output
  · subst k; simp [haltList, finalCfg, single]
  · change (dite (k = M.output) _ _) = update (fun _ => []) M.output _ k
    simp [h]

end Machine

structure Embedding {K K' : Type} [DecidableEq K] [DecidableEq K']
    (Γ : K → Type) (L S : Type) (Γ' : K' → Type) (L' S' : Type) where
  key : K → K'
  symbol : ∀ k, Γ k ≃ Γ' (key k)
  read : S' → S
  write : S' → S → S'
  state : S → S'
  read_state : ∀ v, read (state v) = v
  write_state : ∀ v w, write (state v) w = state w
  stack : (∀ k, List (Γ k)) → ∀ k, List (Γ' k)
  stack_key : ∀ s k, stack s (key k) = (s k).map (symbol k)
  stack_update : ∀ s k x,
    stack (update s k x) = update (stack s) (key k) (x.map (symbol k))
  label : L → L'
  halted : Option L'
  stop : TM2.Stmt Γ' L' S'
  stop_spec : ∀ v s, TM2.stepAux stop (state v) (stack s) = ⟨halted, state v, stack s⟩

namespace Embedding
variable {K K' L S L' S' : Type} [DecidableEq K] [DecidableEq K']
  {Γ : K → Type} {Γ' : K' → Type}
variable (E : Embedding Γ L S Γ' L' S')

def stmt : TM2.Stmt Γ L S → TM2.Stmt Γ' L' S'
  | .push k f q => .push (E.key k) (fun v => E.symbol k (f (E.read v))) (stmt q)
  | .peek k f q => .peek (E.key k)
      (fun v x => E.write v (f (E.read v) (x.map (E.symbol k).symm))) (stmt q)
  | .pop k f q => .pop (E.key k)
      (fun v x => E.write v (f (E.read v) (x.map (E.symbol k).symm))) (stmt q)
  | .load f q => .load (fun v => E.write v (f (E.read v))) (stmt q)
  | .branch f q r => .branch (fun v => f (E.read v)) (stmt q) (stmt r)
  | .goto f => .goto (fun v => E.label (f (E.read v)))
  | .halt => E.stop

def cfg (a : TM2.Cfg Γ L S) : TM2.Cfg Γ' L' S' :=
  ⟨a.l.elim E.halted (fun l => some (E.label l)), E.state a.var, E.stack a.stk⟩

theorem head_map_inverse {α β : Type} (e : α ≃ β) (xs : List α) :
    ((xs.map e).head?).map e.symm = xs.head? := by cases xs <;> simp

theorem stepAux_stmt (q : TM2.Stmt Γ L S) (v : S) (s : ∀ k, List (Γ k)) :
    TM2.stepAux (E.stmt q) (E.state v) (E.stack s) = E.cfg (TM2.stepAux q v s) := by
  induction q generalizing v s with
  | push k f q ih =>
      simp only [stmt, TM2.stepAux, E.read_state, E.stack_key, ← List.map_cons,
        ← E.stack_update]
      exact ih _ _
  | peek k f q ih =>
      simp only [stmt, TM2.stepAux, E.read_state, E.stack_key, head_map_inverse, E.write_state]
      exact ih _ _
  | pop k f q ih =>
      simp only [stmt, TM2.stepAux, E.read_state, E.stack_key, head_map_inverse,
        E.write_state, ← List.map_tail, ← E.stack_update]
      exact ih _ _
  | load f q ih =>
      simp only [stmt, TM2.stepAux, E.read_state, E.write_state]
      exact ih _ _
  | branch f q r ihq ihr =>
      cases h : f v <;> simp only [stmt, TM2.stepAux, E.read_state, h, Bool.cond_false,
        Bool.cond_true]
      · exact ihr _ _
      · exact ihq _ _
  | goto f => simp only [stmt, TM2.stepAux, E.read_state, cfg, Option.elim_some]
  | halt => exact E.stop_spec v s

theorem step_cfg (m : L → TM2.Stmt Γ L S) (m' : L' → TM2.Stmt Γ' L' S')
    (hm : ∀ l, m' (E.label l) = E.stmt (m l))
    (a b : TM2.Cfg Γ L S) (h : TM2.step m a = some b) :
    TM2.step m' (E.cfg a) = some (E.cfg b) := by
  rcases a with ⟨l, v, s⟩
  cases l with
  | none => cases h
  | some l =>
      have hb : b = TM2.stepAux (m l) v s := (Option.some.inj h).symm
      subst b
      simp only [cfg, Option.elim_some, TM2.step, hm]
      exact congrArg some (E.stepAux_stmt (m l) v s)

end Embedding
namespace Compose
variable (M N : Machine)

abbrev Key := M.K ⊕ (Unit ⊕ N.K)
abbrev Label := M.Label ⊕ (Bool ⊕ N.Label)
abbrev State := M.State × N.State × Option Bool

def Alphabet : Key M N → Type
  | .inl k => M.Γ k
  | .inr (.inl _) => Bool
  | .inr (.inr k) => N.Γ k

instance alphabetFinite (k : Key M N) : Fintype (Alphabet M N k) := by
  rcases k with k | (_ | k)
  · exact M.finΓ k
  · exact inferInstanceAs (Fintype Bool)
  · exact N.finΓ k

abbrev phaseLabel (b : Bool) : Label M N := .inr (.inl b)
abbrev auxiliary : Key M N := .inr (.inl ())

def left : Embedding M.Γ M.Label M.State (Alphabet M N) (Label M N) (State M N) where
  key := Sum.inl
  symbol k := Equiv.refl (M.Γ k)
  read := Prod.fst
  write v x := (x, v.2)
  state v := (v, N.initial, none)
  read_state _ := rfl
  write_state _ _ := rfl
  stack s k := match k with
    | .inl j => s j
    | .inr _ => []
  stack_key s k := by exact (List.map_id (s k)).symm
  stack_update s k x := by
    funext j
    rcases j with j | j
    · by_cases h : j = k
      · subst j
        simp only [Function.update_self]
        exact (List.map_id x).symm
      · simp [Function.update_of_ne h, Function.update_of_ne (mt Sum.inl.inj h)]
        rfl
    · simp
  label := Sum.inl
  halted := some (phaseLabel M N false)
  stop := .goto (fun _ => phaseLabel M N false)
  stop_spec _ _ := rfl

def right : Embedding N.Γ N.Label N.State (Alphabet M N) (Label M N) (State M N) where
  key k := .inr (.inr k)
  symbol k := Equiv.refl (N.Γ k)
  read v := v.2.1
  write v x := (v.1, x, v.2.2)
  state v := (M.initial, v, none)
  read_state _ := rfl
  write_state _ _ := rfl
  stack s k := match k with
    | .inl _ => []
    | .inr (.inl _) => []
    | .inr (.inr j) => s j
  stack_key s k := by exact (List.map_id (s k)).symm
  stack_update s k x := by
    funext j
    rcases j with j | (j | j)
    · simp
    · simp
    · by_cases h : j = k
      · subst j
        simp only [Function.update_self]
        exact (List.map_id x).symm
      · simp [Function.update_of_ne h,
          Function.update_of_ne (mt (fun e => Sum.inr.inj (Sum.inr.inj e)) h)]
        rfl
  label l := .inr (.inr l)
  halted := none
  stop := .halt
  stop_spec _ _ := rfl

def source (b : Bool) : Key M N := if b then auxiliary M N else .inl M.output
def target (b : Bool) : Key M N := if b then .inr (.inr N.input) else auxiliary M N

theorem source_ne_target (b : Bool) : source M N b ≠ target M N b := by
  cases b <;> simp [source, target, auxiliary]

def sourceAlphabet : (b : Bool) → Alphabet M N (source M N b) ≃ Bool
  | false => M.outputAlphabet
  | true => Equiv.refl Bool

def targetAlphabet : (b : Bool) → Alphabet M N (target M N b) ≃ Bool
  | false => Equiv.refl Bool
  | true => N.inputAlphabet

def following (b : Bool) : Label M N :=
  if b then .inr (.inr N.main) else phaseLabel M N true

def clean (v : State M N) : State M N := (v.1, v.2.1, none)

def transfer (b : Bool) : TM2.Stmt (Alphabet M N) (Label M N) (State M N) :=
  .pop (source M N b) (fun v c => (v.1, v.2.1, c.map (sourceAlphabet M N b)))
    (.branch (fun v => v.2.2.isSome)
      (.push (target M N b) (fun v => (targetAlphabet M N b).symm (v.2.2.getD false))
        (.load (clean M N) (.goto (fun _ => phaseLabel M N b))))
      (.load (clean M N) (.goto (fun _ => following M N b))))

def code : Label M N → TM2.Stmt (Alphabet M N) (Label M N) (State M N)
  | .inl l => (left M N).stmt (M.code l)
  | .inr (.inl b) => transfer M N b
  | .inr (.inr l) => (right M N).stmt (N.code l)

abbrev machine : Machine where
  K := Key M N
  Γ := Alphabet M N
  input := .inl M.input
  output := .inr (.inr N.output)
  inputAlphabet := M.inputAlphabet
  outputAlphabet := N.outputAlphabet
  Label := Label M N
  main := .inl M.main
  State := State M N
  initial := (M.initial, N.initial, none)
  code := code M N

theorem code_left (l : M.Label) : (machine M N).code ((left M N).label l) =
    (left M N).stmt (M.code l) := rfl

theorem code_right (l : N.Label) : (machine M N).code ((right M N).label l) =
    (right M N).stmt (N.code l) := rfl

theorem initial_left (s : List Bool) : (left M N).cfg (M.initialCfg s) =
    (machine M N).initialCfg s := by
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k
  · by_cases h : k = M.input
    · subst k; simp [Embedding.cfg, left, Machine.initialCfg, Machine.single, machine]; try rfl
    · simp [Embedding.cfg, left, Machine.initialCfg, Machine.single, machine,
        Function.update_of_ne h, Function.update_of_ne (mt Sum.inl.inj h)]; try rfl
  · simp [Embedding.cfg, left, Machine.initialCfg, Machine.single, machine]

theorem final_right (s : List Bool) : (right M N).cfg (N.finalCfg s) =
    (machine M N).finalCfg s := by
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | (k | k)
  · simp [Embedding.cfg, right, Machine.finalCfg, Machine.single, machine]
  · simp [Embedding.cfg, right, Machine.finalCfg, Machine.single, machine]
  · by_cases h : k = N.output
    · subst k; simp [Embedding.cfg, right, Machine.finalCfg, Machine.single, machine]; try rfl
    · simp [Embedding.cfg, right, Machine.finalCfg, Machine.single, machine,
        Function.update_of_ne h,
        Function.update_of_ne (mt (fun e => Sum.inr.inj (Sum.inr.inj e)) h)]; try rfl

end Compose

def twoStacks {K : Type} [DecidableEq K] {Γ : K → Type}
    (a b : K) (xs : List (Γ a)) (ys : List (Γ b)) : ∀ k, List (Γ k) :=
  update (Machine.single a xs) b ys

theorem twoStacks_source {K : Type} [DecidableEq K] {Γ : K → Type}
    {a b : K} (h : a ≠ b) (xs : List (Γ a)) (ys : List (Γ b)) :
    twoStacks a b xs ys a = xs := by
  simp [twoStacks, Machine.single, Function.update_of_ne h]

theorem twoStacks_target {K : Type} [DecidableEq K] {Γ : K → Type}
    (a b : K) (xs : List (Γ a)) (ys : List (Γ b)) :
    twoStacks a b xs ys b = ys := by simp [twoStacks]

theorem twoStacks_move {K : Type} [DecidableEq K] {Γ : K → Type}
    {a b : K} (h : a ≠ b) (x : Γ a) (y : Γ b) (xs : List (Γ a)) (ys : List (Γ b)) :
    update (update (twoStacks a b (x :: xs) ys) a xs) b (y :: ys) =
      twoStacks a b xs (y :: ys) := by
  funext k
  by_cases ha : k = a
  · subst k; simp [twoStacks, Machine.single, Function.update_of_ne h]
  · by_cases hb : k = b
    · subst k; simp [twoStacks, Machine.single]
    · simp [twoStacks, Machine.single, Function.update_of_ne ha, Function.update_of_ne hb]

theorem twoStacks_pop_empty {K : Type} [DecidableEq K] {Γ : K → Type}
    {a b : K} (h : a ≠ b) (ys : List (Γ b)) :
    update (twoStacks a b [] ys) a [] = twoStacks a b [] ys := by
  funext k
  by_cases ha : k = a
  · subst k; simp [twoStacks, Machine.single, Function.update_of_ne h]
  · simp [Function.update_of_ne ha]

namespace Compose
variable (M N : Machine)

def transferCfg (b : Bool) (xs ys : List Bool) : (machine M N).Cfg :=
  ⟨some (phaseLabel M N b), (M.initial, N.initial, none),
    twoStacks (source M N b) (target M N b)
      (xs.map (sourceAlphabet M N b).symm) (ys.map (targetAlphabet M N b).symm)⟩

def boundaryCfg (b : Bool) (ys : List Bool) : (machine M N).Cfg :=
  ⟨some (following M N b), (M.initial, N.initial, none),
    twoStacks (source M N b) (target M N b) [] (ys.map (targetAlphabet M N b).symm)⟩

theorem transfer_cons (b x : Bool) (xs ys : List Bool) :
    (machine M N).step (transferCfg M N b (x :: xs) ys) =
      some (transferCfg M N b xs (x :: ys)) := by
  change some (TM2.stepAux (transfer M N b) (M.initial, N.initial, none)
    (twoStacks (source M N b) (target M N b)
      ((x :: xs).map (sourceAlphabet M N b).symm)
      (ys.map (targetAlphabet M N b).symm))) = _
  simp only [transfer, TM2.stepAux, List.map_cons]
  rw [twoStacks_source (source_ne_target M N b)]
  simp only [List.head?_cons, List.tail_cons, Option.map_some, Equiv.apply_symm_apply,
    Option.isSome_some, Bool.cond_true, Option.getD_some, clean]
  rw [Function.update_of_ne (Ne.symm (source_ne_target M N b)), twoStacks_target]
  rw [twoStacks_move (source_ne_target M N b)]
  rfl

theorem transfer_empty (b : Bool) (ys : List Bool) :
    (machine M N).step (transferCfg M N b [] ys) = some (boundaryCfg M N b ys) := by
  change some (TM2.stepAux (transfer M N b) (M.initial, N.initial, none)
    (twoStacks (source M N b) (target M N b) []
      (ys.map (targetAlphabet M N b).symm))) = _
  simp only [transfer, TM2.stepAux]
  rw [twoStacks_source (source_ne_target M N b)]
  simp only [List.head?_nil, List.tail_nil, Option.map_none, Option.isSome_none,
    Bool.cond_false, clean]
  rw [twoStacks_pop_empty (source_ne_target M N b)]
  rfl

theorem left_final (ys : List Bool) :
    (left M N).cfg (M.finalCfg ys) = transferCfg M N false ys [] := by
  apply cfg_ext <;> try rfl
  funext j
  rcases j with j | (j | j)
  · by_cases h : j = M.output
    · subst j
      simp [Embedding.cfg, left, Machine.finalCfg, Machine.single, transferCfg,
        twoStacks, source, target, sourceAlphabet, targetAlphabet, auxiliary]; try rfl
    · simp [Embedding.cfg, left, Machine.finalCfg, Machine.single, transferCfg,
        twoStacks, source, target, sourceAlphabet, targetAlphabet, auxiliary,
        Function.update_of_ne h, Function.update_of_ne (mt Sum.inl.inj h)]; rfl
  · simp [Embedding.cfg, left, Machine.finalCfg, Machine.single, transferCfg,
      twoStacks, source, target, sourceAlphabet, targetAlphabet, auxiliary]
  · simp [Embedding.cfg, left, Machine.finalCfg, Machine.single, transferCfg,
      twoStacks, source, target, sourceAlphabet, targetAlphabet, auxiliary]

theorem boundary_false (ys : List Bool) :
    boundaryCfg M N false ys = transferCfg M N true ys [] := by
  apply cfg_ext <;> try rfl
  funext j
  rcases j with j | (j | j)
  · by_cases h : j = M.output
    · subst j
      simp [boundaryCfg, transferCfg, twoStacks, Machine.single, source, target,
        sourceAlphabet, targetAlphabet, auxiliary]
    · simp [boundaryCfg, transferCfg, twoStacks, Machine.single, source, target,
        sourceAlphabet, targetAlphabet, auxiliary]
  · cases j
    simp [boundaryCfg, transferCfg, twoStacks, Machine.single, source, target,
      sourceAlphabet, targetAlphabet, auxiliary]; try rfl
    exact ⟨fun _ => rfl, fun _ => rfl⟩
  · by_cases h : j = N.input
    · subst j
      simp [boundaryCfg, transferCfg, twoStacks, Machine.single, source, target,
        sourceAlphabet, targetAlphabet, auxiliary]
    · simp [boundaryCfg, transferCfg, twoStacks, Machine.single, source, target,
        sourceAlphabet, targetAlphabet, auxiliary,
        Function.update_of_ne (mt (fun e => Sum.inr.inj (Sum.inr.inj e)) h)]

theorem boundary_true (ys : List Bool) :
    boundaryCfg M N true ys = (right M N).cfg (N.initialCfg ys) := by
  apply cfg_ext <;> try rfl
  funext j
  rcases j with j | (j | j)
  · simp [boundaryCfg, twoStacks, Machine.single, source, target, targetAlphabet,
      auxiliary, Embedding.cfg, right, Machine.initialCfg]
  · cases j
    simp [boundaryCfg, twoStacks, Machine.single, source, target, targetAlphabet,
      auxiliary, Embedding.cfg, right, Machine.initialCfg]
  · by_cases h : j = N.input
    · subst j
      simp [boundaryCfg, twoStacks, Machine.single, source, target, targetAlphabet,
        auxiliary, Embedding.cfg, right, Machine.initialCfg]; try rfl
    · simp [boundaryCfg, twoStacks, Machine.single, source, target, targetAlphabet,
        auxiliary, Embedding.cfg, right, Machine.initialCfg, Function.update_of_ne h,
        Function.update_of_ne (mt (fun e => Sum.inr.inj (Sum.inr.inj e)) h)]; rfl

end Compose

namespace Machine
variable {K L S : Type} {Γ : K → Type} [DecidableEq K]

def pushes : TM2.Stmt Γ L S → ℕ
  | .push _ _ q => 1+pushes q
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q r => max (pushes q) (pushes r)
  | .goto _ => 0
  | .halt => 0

variable [Fintype K]

def growth (M : Machine) : ℕ := ∑ l, pushes (M.code l)

end Machine

end MetricKMedian.Complexity.FiniteComposition

end Inline_PCPInherited

end OAI
end


