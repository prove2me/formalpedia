-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_common_refinement_points_F000
-- name    : ProbabilityTheory_chapter_01_thm_1_1_common_refinement_points_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T22:47:34.807094+00:00
-- url     : https://prove2.me/theorems/d426f280-83ab-400e-b81b-40263a453153
-- title:
--   Chapter 1, thm_1_1_common_refinement_points: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_1_common_refinement_points`: `DarbouxCommonRefinementSandwich`, `partitionPointSet`, `mem_partitionPointSet_iff`, `partitionPointSet_left_mem`, `partitionPointSet_right_mem`, and 29 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_common_refinement_points.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_darboux_gap_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F000
import Mathlib.Data.List.GetD
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute

def DarbouxCommonRefinementSandwich
    (a b : ℝ) (f α : ℝ → ℝ) : Prop :=
  ∀ δ > 0, ∀ P Q : Partition a b,
    P.mesh < δ →
    Q.mesh < δ →
      ∃ R : Partition a b,
        R.mesh < δ ∧
        lowerSum P f α ≤ lowerSum R f α ∧
        lowerSum Q f α ≤ lowerSum R f α ∧
        upperSum R f α ≤ upperSum P f α ∧
        upperSum R f α ≤ upperSum Q f α

noncomputable def partitionPointSet {a b : ℝ}
    (P : Partition a b) : Finset ℝ :=
  (Finset.univ : Finset (Fin (P.n + 1))).image P.pts
lemma mem_partitionPointSet_iff {a b x : ℝ}
    (P : Partition a b) :
    x ∈ partitionPointSet P ↔ ∃ i : Fin (P.n + 1), P.pts i = x := by
  simp [partitionPointSet, eq_comm]
lemma partitionPointSet_left_mem {a b : ℝ}
    (P : Partition a b) :
    a ∈ partitionPointSet P := by
  rw [mem_partitionPointSet_iff]
  exact ⟨0, P.pts_start⟩
lemma partitionPointSet_right_mem {a b : ℝ}
    (P : Partition a b) :
    b ∈ partitionPointSet P := by
  rw [mem_partitionPointSet_iff]
  exact ⟨Fin.last P.n, P.pts_end⟩
lemma partitionPointSet_subset_Icc {a b x : ℝ}
    (P : Partition a b)
    (hx : x ∈ partitionPointSet P) :
    x ∈ Icc a b := by
  rcases (mem_partitionPointSet_iff P).1 hx with ⟨i, rfl⟩
  exact DarbouxRS.partition_pts_mem_Icc_core P

noncomputable def commonRefinementPointSet {a b : ℝ}
    (P Q : Partition a b) : Finset ℝ :=
  partitionPointSet P ∪ partitionPointSet Q

noncomputable def commonRefinementPointList {a b : ℝ}
    (P Q : Partition a b) : List ℝ :=
  (commonRefinementPointSet P Q).sort (fun x y : ℝ => x ≤ y)
lemma mem_commonRefinementPointList_iff {a b x : ℝ}
    (P Q : Partition a b) :
    x ∈ commonRefinementPointList P Q ↔
      x ∈ partitionPointSet P ∨ x ∈ partitionPointSet Q := by
  unfold commonRefinementPointList commonRefinementPointSet
  rw [Finset.mem_sort, Finset.mem_union]
lemma commonRefinementPointList_sorted {a b : ℝ}
    (P Q : Partition a b) :
    (commonRefinementPointList P Q).Pairwise (fun x y : ℝ => x ≤ y) := by
  unfold commonRefinementPointList
  exact Finset.pairwise_sort (commonRefinementPointSet P Q) (fun x y : ℝ => x ≤ y)
lemma commonRefinementPointList_nodup {a b : ℝ}
    (P Q : Partition a b) :
    (commonRefinementPointList P Q).Nodup := by
  unfold commonRefinementPointList
  exact Finset.sort_nodup (commonRefinementPointSet P Q) (fun x y : ℝ => x ≤ y)
lemma commonRefinementPointList_left_mem {a b : ℝ}
    (P Q : Partition a b) :
    a ∈ commonRefinementPointList P Q := by
  rw [mem_commonRefinementPointList_iff]
  exact Or.inl (partitionPointSet_left_mem P)
lemma commonRefinementPointList_right_mem {a b : ℝ}
    (P Q : Partition a b) :
    b ∈ commonRefinementPointList P Q := by
  rw [mem_commonRefinementPointList_iff]
  exact Or.inl (partitionPointSet_right_mem P)
lemma commonRefinementPointList_covers_left {a b : ℝ}
    (P Q : Partition a b) (i : Fin (P.n + 1)) :
    P.pts i ∈ commonRefinementPointList P Q := by
  rw [mem_commonRefinementPointList_iff]
  exact Or.inl ((mem_partitionPointSet_iff P).2 ⟨i, rfl⟩)
lemma commonRefinementPointList_covers_right {a b : ℝ}
    (P Q : Partition a b) (i : Fin (Q.n + 1)) :
    Q.pts i ∈ commonRefinementPointList P Q := by
  rw [mem_commonRefinementPointList_iff]
  exact Or.inr ((mem_partitionPointSet_iff Q).2 ⟨i, rfl⟩)
lemma commonRefinementPointList_subset_Icc {a b x : ℝ}
    (P Q : Partition a b)
    (hx : x ∈ commonRefinementPointList P Q) :
    x ∈ Icc a b := by
  rcases (mem_commonRefinementPointList_iff P Q).1 hx with hxP | hxQ
  · exact partitionPointSet_subset_Icc P hxP
  · exact partitionPointSet_subset_Icc Q hxQ
lemma sorted_nodup_adjacent_lt {l : List ℝ}
    (hsorted : l.Pairwise (fun x y : ℝ => x ≤ y))
    (hnodup : l.Nodup) {i : ℕ}
    (hi : i + 1 < l.length) :
    l[i] < l[i + 1] := by
  have hi0 : i < l.length := Nat.lt_trans (Nat.lt_succ_self i) hi
  have hle : l[i] ≤ l[i + 1] :=
    (List.pairwise_iff_getElem.mp hsorted) i (i + 1) hi0 hi (Nat.lt_succ_self i)
  have hne : l[i] ≠ l[i + 1] := by
    intro hEq
    have hidx : i = i + 1 := by
      exact (List.Nodup.getElem_inj_iff (l := l) hnodup (i := i) (hi := hi0)
        (j := i + 1) (hj := hi)).1 hEq
    omega
  exact lt_of_le_of_ne hle hne
lemma commonRefinementPointList_adjacent_lt {a b : ℝ}
    (P Q : Partition a b) {i : ℕ}
    (hi : i + 1 < (commonRefinementPointList P Q).length) :
    (commonRefinementPointList P Q)[i] <
      (commonRefinementPointList P Q)[i + 1] :=
  sorted_nodup_adjacent_lt
    (commonRefinementPointList_sorted P Q)
    (commonRefinementPointList_nodup P Q) hi
lemma sorted_nodup_adjacent_getD_lt {l : List ℝ} {fallback : ℝ}
    (hsorted : l.Pairwise (fun x y : ℝ => x ≤ y))
    (hnodup : l.Nodup) {i : ℕ}
    (hi : i + 1 < l.length) :
    l.getD i fallback < l.getD (i + 1) fallback := by
  have hi0 : i < l.length := Nat.lt_trans (Nat.lt_succ_self i) hi
  rw [List.getD_eq_getElem l fallback hi0]
  rw [List.getD_eq_getElem l fallback hi]
  exact sorted_nodup_adjacent_lt hsorted hnodup hi
lemma commonRefinementPointList_adjacent_getD_lt {a b : ℝ}
    (P Q : Partition a b) {i : ℕ}
    (hi : i + 1 < (commonRefinementPointList P Q).length) :
    (commonRefinementPointList P Q).getD i b <
      (commonRefinementPointList P Q).getD (i + 1) b :=
  sorted_nodup_adjacent_getD_lt
    (commonRefinementPointList_sorted P Q)
    (commonRefinementPointList_nodup P Q) hi
lemma partition_endpoints_lt {a b : ℝ} (P : Partition a b) :
    a < b := by
  have hzero_last : (0 : Fin (P.n + 1)) < Fin.last P.n := by
    change 0 < P.n
    exact P.hn
  calc
    a = P.pts 0 := P.pts_start.symm
    _ < P.pts (Fin.last P.n) := P.strict_mono hzero_last
    _ = b := P.pts_end
lemma list_length_two_le_of_nodup_mem_ne {l : List ℝ} {a b : ℝ}
    (_hnodup : l.Nodup) (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) :
    2 ≤ l.length := by
  rcases List.mem_iff_getElem.1 ha with ⟨i, hi, hia⟩
  rcases List.mem_iff_getElem.1 hb with ⟨j, hj, hjb⟩
  have hij : i ≠ j := by
    intro h
    subst j
    apply hne
    exact hia.symm.trans hjb
  omega
lemma sorted_list_getD_zero_eq_left {l : List ℝ} {a b : ℝ}
    (hsorted : l.Pairwise (fun x y : ℝ => x ≤ y))
    (ha : a ∈ l)
    (hsub : ∀ {x : ℝ}, x ∈ l → x ∈ Icc a b) :
    l.getD 0 b = a := by
  have hlen : 0 < l.length := by
    rcases List.mem_iff_getElem.1 ha with ⟨i, hi, _⟩
    omega
  have hhead_mem : l[0] ∈ l := by
    exact List.getElem_mem (l := l) (n := 0) hlen
  have hge : a ≤ l[0] := (hsub hhead_mem).1
  have hle : l[0] ≤ a := by
    rcases List.mem_iff_getElem.1 ha with ⟨j, hj, hjv⟩
    by_cases hj0 : j = 0
    · subst j
      exact le_of_eq hjv
    · have h0j : 0 < j := Nat.pos_of_ne_zero hj0
      have hle0j :=
        (List.pairwise_iff_getElem.mp hsorted) 0 j hlen hj h0j
      simpa [hjv] using hle0j
  have hEq : l[0] = a := le_antisymm hle hge
  rw [List.getD_eq_getElem l b hlen]
  exact hEq
lemma sorted_list_getD_last_eq_right {l : List ℝ} {a b : ℝ}
    (hsorted : l.Pairwise (fun x y : ℝ => x ≤ y))
    (hb : b ∈ l)
    (hsub : ∀ {x : ℝ}, x ∈ l → x ∈ Icc a b) :
    l.getD (l.length - 1) a = b := by
  have hlen : 0 < l.length := by
    rcases List.mem_iff_getElem.1 hb with ⟨i, hi, _⟩
    omega
  have hlast : l.length - 1 < l.length := by omega
  have hlast_mem : l[l.length - 1] ∈ l := by
    exact List.getElem_mem (l := l) (n := l.length - 1) hlast
  have hle : l[l.length - 1] ≤ b := (hsub hlast_mem).2
  have hge : b ≤ l[l.length - 1] := by
    rcases List.mem_iff_getElem.1 hb with ⟨j, hj, hjv⟩
    by_cases hjlast : j = l.length - 1
    · subst j
      exact le_of_eq hjv.symm
    · have hj_lt_last : j < l.length - 1 := by omega
      have hle_last :=
        (List.pairwise_iff_getElem.mp hsorted) j (l.length - 1) hj hlast hj_lt_last
      simpa [hjv] using hle_last
  have hEq : l[l.length - 1] = b := le_antisymm hle hge
  rw [List.getD_eq_getElem l a hlast]
  exact hEq
lemma commonRefinementPointList_length_two_le {a b : ℝ}
    (P Q : Partition a b) :
    2 ≤ (commonRefinementPointList P Q).length := by
  refine list_length_two_le_of_nodup_mem_ne
    (commonRefinementPointList_nodup P Q)
    (commonRefinementPointList_left_mem P Q)
    (commonRefinementPointList_right_mem P Q) ?_
  exact ne_of_lt (partition_endpoints_lt P)
lemma commonRefinementPointList_getD_zero {a b : ℝ}
    (P Q : Partition a b) :
    (commonRefinementPointList P Q).getD 0 b = a := by
  exact sorted_list_getD_zero_eq_left
    (commonRefinementPointList_sorted P Q)
    (commonRefinementPointList_left_mem P Q)
    (fun hx => commonRefinementPointList_subset_Icc P Q hx)
lemma commonRefinementPointList_getD_last {a b : ℝ}
    (P Q : Partition a b) :
    (commonRefinementPointList P Q).getD
      ((commonRefinementPointList P Q).length - 1) a = b := by
  exact sorted_list_getD_last_eq_right
    (commonRefinementPointList_sorted P Q)
    (commonRefinementPointList_right_mem P Q)
    (fun hx => commonRefinementPointList_subset_Icc P Q hx)
lemma partition_length_le_mesh_core {a b : ℝ}
    (P : Partition a b) (i : Fin P.n) :
    P.pts i.succ - P.pts i.castSucc ≤ P.mesh := by
  unfold Partition.mesh
  exact Finset.le_sup'
    (fun j : Fin P.n => P.pts j.succ - P.pts j.castSucc)
    (Finset.mem_univ i)
lemma sorted_nodup_adjacent_no_mem_between {l : List ℝ} {fallback z : ℝ}
    (hsorted : l.Pairwise (fun x y : ℝ => x ≤ y))
    {i : ℕ}
    (hi : i + 1 < l.length)
    (hz : z ∈ l) :
    ¬ (l.getD i fallback < z ∧ z < l.getD (i + 1) fallback) := by
  intro hbetween
  have hi0 : i < l.length := Nat.lt_trans (Nat.lt_succ_self i) hi
  rw [List.getD_eq_getElem l fallback hi0] at hbetween
  rw [List.getD_eq_getElem l fallback hi] at hbetween
  rcases hbetween with ⟨hleft, hright⟩
  rcases List.mem_iff_getElem.1 hz with ⟨k, hk, hkz⟩
  by_cases hki : k ≤ i
  · have hle_left : z ≤ l[i] := by
      by_cases hki_eq : k = i
      · subst k
        exact le_of_eq hkz.symm
      · have hk_lt_i : k < i := lt_of_le_of_ne hki hki_eq
        have hleki :=
          (List.pairwise_iff_getElem.mp hsorted) k i hk hi0 hk_lt_i
        simpa [hkz] using hleki
    linarith
  · have hik : i + 1 ≤ k := by omega
    have hle_right : l[i + 1] ≤ z := by
      by_cases hk_eq : k = i + 1
      · subst k
        exact le_of_eq hkz
      · have hlt : i + 1 < k := lt_of_le_of_ne hik (Ne.symm hk_eq)
        have hleik :=
          (List.pairwise_iff_getElem.mp hsorted) (i + 1) k hi hk hlt
        simpa [hkz] using hleik
    linarith
lemma list_getD_mem_of_lt {l : List ℝ} {fallback : ℝ} {i : ℕ}
    (hi : i < l.length) :
    l.getD i fallback ∈ l := by
  rw [List.getD_eq_getElem l fallback hi]
  exact List.getElem_mem (l := l) (n := i) hi
lemma commonRefinementPointList_adjacent_right_le_next_of_left_partition
    {a b : ℝ} (P Q : Partition a b) {i : ℕ} (k : Fin (P.n + 1))
    (hi : i + 1 < (commonRefinementPointList P Q).length)
    (hleft : (commonRefinementPointList P Q).getD i b = P.pts k) :
    ∃ j : Fin P.n,
      P.pts j.castSucc = P.pts k ∧
        (commonRefinementPointList P Q).getD (i + 1) b ≤ P.pts j.succ := by
  let l := commonRefinementPointList P Q
  have hsorted : l.Pairwise (fun x y : ℝ => x ≤ y) :=
    commonRefinementPointList_sorted P Q
  have hnodup : l.Nodup := commonRefinementPointList_nodup P Q
  have hgap : l.getD i b < l.getD (i + 1) b :=
    commonRefinementPointList_adjacent_getD_lt P Q hi
  have hright_mem : l.getD (i + 1) b ∈ l :=
    list_getD_mem_of_lt (l := l) (fallback := b) hi
  have hright_le_b : l.getD (i + 1) b ≤ b :=
    (commonRefinementPointList_subset_Icc P Q hright_mem).2
  have hklt : k.val < P.n := by
    by_contra hnot
    have hk_val : k.val = P.n := by omega
    have hk_eq : k = Fin.last P.n := Fin.ext hk_val
    have hleft_b : l.getD i b = b := by
      rw [hleft, hk_eq, P.pts_end]
    linarith
  let j : Fin P.n := ⟨k.val, hklt⟩
  have hjk : P.pts j.castSucc = P.pts k := by
    congr 1
  refine ⟨j, hjk, ?_⟩
  by_contra hnot
  have hnext_lt_right : P.pts j.succ < l.getD (i + 1) b :=
    lt_of_not_ge hnot
  have hleft_lt_next : l.getD i b < P.pts j.succ := by
    rw [hleft, ← hjk]
    exact P.strict_mono Fin.castSucc_lt_succ
  have hnext_mem : P.pts j.succ ∈ l :=
    commonRefinementPointList_covers_left P Q j.succ
  exact (sorted_nodup_adjacent_no_mem_between hsorted hi hnext_mem)
    ⟨hleft_lt_next, hnext_lt_right⟩
lemma commonRefinementPointList_adjacent_right_le_next_of_right_partition
    {a b : ℝ} (P Q : Partition a b) {i : ℕ} (k : Fin (Q.n + 1))
    (hi : i + 1 < (commonRefinementPointList P Q).length)
    (hleft : (commonRefinementPointList P Q).getD i b = Q.pts k) :
    ∃ j : Fin Q.n,
      Q.pts j.castSucc = Q.pts k ∧
        (commonRefinementPointList P Q).getD (i + 1) b ≤ Q.pts j.succ := by
  let l := commonRefinementPointList P Q
  have hsorted : l.Pairwise (fun x y : ℝ => x ≤ y) :=
    commonRefinementPointList_sorted P Q
  have hgap : l.getD i b < l.getD (i + 1) b :=
    commonRefinementPointList_adjacent_getD_lt P Q hi
  have hright_mem : l.getD (i + 1) b ∈ l :=
    list_getD_mem_of_lt (l := l) (fallback := b) hi
  have hright_le_b : l.getD (i + 1) b ≤ b :=
    (commonRefinementPointList_subset_Icc P Q hright_mem).2
  have hklt : k.val < Q.n := by
    by_contra hnot
    have hk_val : k.val = Q.n := by omega
    have hk_eq : k = Fin.last Q.n := Fin.ext hk_val
    have hleft_b : l.getD i b = b := by
      rw [hleft, hk_eq, Q.pts_end]
    linarith
  let j : Fin Q.n := ⟨k.val, hklt⟩
  have hjk : Q.pts j.castSucc = Q.pts k := by
    congr 1
  refine ⟨j, hjk, ?_⟩
  by_contra hnot
  have hnext_lt_right : Q.pts j.succ < l.getD (i + 1) b :=
    lt_of_not_ge hnot
  have hleft_lt_next : l.getD i b < Q.pts j.succ := by
    rw [hleft, ← hjk]
    exact Q.strict_mono Fin.castSucc_lt_succ
  have hnext_mem : Q.pts j.succ ∈ l :=
    commonRefinementPointList_covers_right P Q j.succ
  exact (sorted_nodup_adjacent_no_mem_between hsorted hi hnext_mem)
    ⟨hleft_lt_next, hnext_lt_right⟩
lemma commonRefinementPointList_adjacent_length_le_mesh_of_left_partition
    {a b : ℝ} (P Q : Partition a b) {i : ℕ} (k : Fin (P.n + 1))
    (hi : i + 1 < (commonRefinementPointList P Q).length)
    (hleft : (commonRefinementPointList P Q).getD i b = P.pts k) :
    (commonRefinementPointList P Q).getD (i + 1) b -
        (commonRefinementPointList P Q).getD i b ≤ P.mesh := by
  let l := commonRefinementPointList P Q
  rcases commonRefinementPointList_adjacent_right_le_next_of_left_partition
      P Q k hi hleft with ⟨j, hjk, hright_le_next⟩
  have hlen_le :
      l.getD (i + 1) b - l.getD i b ≤ P.pts j.succ - P.pts j.castSucc := by
    rw [hleft, ← hjk]
    linarith
  exact le_trans hlen_le (partition_length_le_mesh_core P j)
lemma commonRefinementPointList_adjacent_length_le_mesh_of_right_partition
    {a b : ℝ} (P Q : Partition a b) {i : ℕ} (k : Fin (Q.n + 1))
    (hi : i + 1 < (commonRefinementPointList P Q).length)
    (hleft : (commonRefinementPointList P Q).getD i b = Q.pts k) :
    (commonRefinementPointList P Q).getD (i + 1) b -
        (commonRefinementPointList P Q).getD i b ≤ Q.mesh := by
  let l := commonRefinementPointList P Q
  rcases commonRefinementPointList_adjacent_right_le_next_of_right_partition
      P Q k hi hleft with ⟨j, hjk, hright_le_next⟩
  have hlen_le :
      l.getD (i + 1) b - l.getD i b ≤ Q.pts j.succ - Q.pts j.castSucc := by
    rw [hleft, ← hjk]
    linarith
  exact le_trans hlen_le (partition_length_le_mesh_core Q j)
end Thm11SourceRoute


