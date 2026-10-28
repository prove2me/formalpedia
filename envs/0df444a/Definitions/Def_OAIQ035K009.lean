-- Prove2me | Definitions.Def_OAIQ035K009
-- name    : OAIQ035K009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T07:53:55.231361+00:00
-- url     : https://prove2.me/theorems/596fcbb2-db3f-4ad2-a820-668bb69fdb3e
-- title:
--   Definitions bundle OAIQ035K009 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 42 declarations of OpenAI's Lean: 18 definitions, 2 inductive types or structures and 22 theorems. The definitions and types are `OAI.MetricKMedian.Preparation.RationalIntervals.height`, `OAI.MetricKMedian.Preparation.RationalIntervals.length`, `OAI.MetricKMedian.Preparation.RationalIntervals.previous`, `OAI.MetricKMedian.Preparation.RationalSplitting.Piece`, `OAI.MetricKMedian.Preparation.RationalSplitting.assigned`, `OAI.MetricKMedian.Preparation.RationalSplitting.assignment`, `OAI.MetricKMedian.Preparation.RationalSplitting.count`, `OAI.MetricKMedian.Preparation.RationalSplitting.cuts`, `OAI.MetricKMedian.Preparation.RationalSplitting.index`, `OAI.MetricKMedian.Preparation.RationalSplitting.input`, `OAI.MetricKMedian.Preparation.RationalSplitting.original`, `OAI.MetricKMedian.Preparation.RationalSplitting.weight`, `OAI.MetricKMedian.Preparation.RationalSplitting.weights`, `OAI.MetricKMedian.Preparation.RationalUnitInput`, `OAI.MetricKMedian.Preparation.RationalUnitInput.Realization`, `OAI.MetricKMedian.TruncatedLP.nearMass`, `OAI.MetricKMedian.TruncatedLP.nearWeight`, `OAI.MetricKMedian.TruncatedLP.repairedAssignment`, `OAI.MetricKMedian.TruncatedLP.repairedOpening`, `OAI.MetricKMedian.rationalArgmin`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Geometry_RationalIntervals`, `KMedian_Geometry_RationalSplitEnumeration`, `KMedian_Geometry_RationalSplitInput`, `KMedian_Geometry_RationalSplitting`, `KMedian_Geometry_RationalUnitInput`, `KMedian_Optimization_RationalArgmin`, `KMedian_Optimization_TruncatedRepair`, `KMedian_Reduction_NormalizationGuesses`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K022`, `OAIQ035K023`, `OAIQ035K024` and `OAIQ035K062`; the statement `OAI_MetricKMedian_CopyState_valid_advance`; the proofs of `OAI_MetricKMedian_CopyState_valid_advance` and `OAI_MetricKMedian_GraphComparison_uniform_drift_le`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalIntervals
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
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalSplitting
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
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalSplitEnumeration
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
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalUnitInput
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

namespace RationalUnitInput
variable {f j : ℕ} (U : RationalUnitInput f j)

structure Realization (X : Type) [PseudoMetricSpace X] where
  i : Fin f → X
  c : Fin j → X
  hdf : ∀ a b, dist (i a) (i b)=(U.df a b:ℝ)
  hdc : ∀ c' a, dist (c c') (i a)=(U.dc c' a:ℝ)
  hdd : ∀ c' c'', dist (c c') (c c'')=(U.dd c' c'':ℝ)

end RationalUnitInput
end MetricKMedian.Preparation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalSplitInput
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
-- module Solutions.OAIQ035_KM.KMedian_Optimization_RationalArgmin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian
open Finset

def rationalArgmin (A : Finset ℚ) (f : ℚ → ℚ) : ℚ :=
  if hA : A.Nonempty then
    let v := (A.image f).min' (hA.image f)
    let B := A.filter (fun t => f t=v)
    if hB : B.Nonempty then B.min' hB else 0
  else 0

end MetricKMedian
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_TruncatedRepair
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

def nearWeight (d x : κ → ι → ℚ) (j : κ) (i : ι) : ℚ :=
  if d j i ≤ 1 then x j i else 0

def nearMass (d x : κ → ι → ℚ) (j : κ) : ℚ := ∑ i, nearWeight d x j i

def repairedOpening (y : ι → ℚ) (ρ : ℚ) (i : ι) : ℚ := min 1 (y i/(1-ρ))

def repairedAssignment (d x : κ → ι → ℚ) (j : κ) (i : ι) : ℚ :=
  nearWeight d x j i/nearMass d x j

omit [Fintype ι] [Fintype κ] in
theorem nearWeight_nonneg (d x : κ → ι → ℚ) (hx : ∀ j i, 0 ≤ x j i) (j : κ) (i : ι) :
    0 ≤ nearWeight d x j i := by
  unfold nearWeight
  split_ifs
  · exact hx j i
  · exact le_rfl

omit [Fintype ι] [Fintype κ] in
theorem nearWeight_le (d x : κ → ι → ℚ) (hx : ∀ j i, 0 ≤ x j i) (j : κ) (i : ι) :
    nearWeight d x j i ≤ x j i := by unfold nearWeight; split_ifs <;> simp_all

end MetricKMedian.TruncatedLP
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_NormalizationGuesses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian
open Finset

namespace Normalization

theorem dyadic_bracket (c d : ℚ) (N : ℕ) (hd : 0 < d) (hc : d ≤ c)
    (hupper : c ≤ d*(2:ℚ)^N) :
    ∃ t ≤ N, c ≤ d*(2:ℚ)^t ∧ d*(2:ℚ)^t ≤ 2*c := by
  induction N with
  | zero =>
    refine ⟨0,le_rfl,hupper,?_⟩
    simp only [pow_zero,mul_one]
    linarith
  | succ N ih =>
    by_cases h : c ≤ d*(2:ℚ)^N
    · obtain ⟨t,ht,h1,h2⟩ := ih h
      exact ⟨t,by omega,h1,h2⟩
    · refine ⟨N+1,le_rfl,hupper,?_⟩
      rw [pow_succ]
      have hh := lt_of_not_ge h
      nlinarith

end Normalization
end MetricKMedian
end
end

end OAI
end


