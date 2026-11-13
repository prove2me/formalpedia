-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_common_refinement_monotonicity_F000
-- name    : ProbabilityTheory_chapter_01_thm_1_1_common_refinement_monotonicity_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T23:01:32.156374+00:00
-- url     : https://prove2.me/theorems/9e4460f1-1812-48fe-b092-4f5493fed043
-- title:
--   Chapter 1, thm_1_1_common_refinement_monotonicity: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_1_common_refinement_monotonicity`: `DarbouxPartitionRefines`, `DarbouxPartitionRefines.index`, `DarbouxPartitionRefines.indexD`, `DarbouxPartitionRefines.index_le`, `DarbouxPartitionRefines.index_pts`, and 31 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_common_refinement_monotonicity.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_common_refinement_points_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_common_refinement_points_F001
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F000
import Mathlib.Data.List.GetD
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

namespace DarbouxRS
/--
The integrator function `alpha` does not decrease across any subinterval of the partition.

Because `alpha` is assumed to be monotonic on `[a, b]` (via `SourceHypotheses`), and the
partition points strictly increase (`x_i < x_{i+1}`), the difference `alpha(x_{i+1}) - alpha(x_i)`
is always non-negative. This guarantees that the width/weights in the Riemann-Stieltjes sum
are non-negative.
-/
private lemma partition_increment_nonneg_of_source_core_local {a b : ℝ} (P : Partition a b)
    {f alpha : ℝ → ℝ} (hs : SourceHypotheses a b f alpha) {i : Fin P.n} :
    0 ≤ alpha (P.pts i.succ) - alpha (P.pts i.castSucc) := by
  -- Unpack the SourceHypotheses to get the monotonicity of alpha
  rcases hs with ⟨_hab, _hAbove, _hBelow, hmono⟩

  -- The endpoints of the subinterval are in [a, b]
  have hleft : P.pts i.castSucc ∈ Set.Icc a b := partition_pts_mem_Icc_core P
  have hright : P.pts i.succ ∈ Set.Icc a b := partition_pts_mem_Icc_core P

  -- Because x_i < x_{i+1}, monotonicity implies alpha(x_i) ≤ alpha(x_{i+1})
  have h_pts_lt : P.pts i.castSucc < P.pts i.succ :=
    P.strict_mono (Fin.castSucc_lt_succ)

  exact sub_nonneg.mpr (hmono hleft hright (le_of_lt h_pts_lt))
end DarbouxRS

namespace Thm11SourceRoute

private lemma partitionOfStrictEndpointList_mem_node_local {a b : ℝ} (l : List ℝ)
    (hlen : 2 ≤ l.length)
    (hstart : l.getD 0 b = a)
    (hend : l.getD (l.length - 1) a = b)
    (hstrict : ∀ {i : ℕ}, i + 1 < l.length → l.getD i b < l.getD (i + 1) b)
    {x : ℝ} (hx : x ∈ l) :
    ∃ j : Fin ((partitionOfStrictEndpointList l hlen hstart hend hstrict).n + 1),
      (partitionOfStrictEndpointList l hlen hstart hend hstrict).pts j = x := by
  rcases List.mem_iff_getElem.1 hx with ⟨j, hj, hjx⟩
  have hjFin : j < (partitionOfStrictEndpointList l hlen hstart hend hstrict).n + 1 := by
    simp [partitionOfStrictEndpointList]
    omega
  refine ⟨⟨j, hjFin⟩, ?_⟩
  change l.getD j b = x
  rw [List.getD_eq_getElem l b hj]
  exact hjx

private lemma commonRefinementPointList_adjacent_length_lt_delta_local {a b δ : ℝ}
    (P Q : Partition a b)
    (hPmesh : P.mesh < δ) (hQmesh : Q.mesh < δ)
    {i : ℕ}
    (hi : i + 1 < (commonRefinementPointList P Q).length) :
    (commonRefinementPointList P Q).getD (i + 1) b -
        (commonRefinementPointList P Q).getD i b < δ := by
  let l := commonRefinementPointList P Q
  have hi0 : i < l.length := Nat.lt_trans (Nat.lt_succ_self i) hi
  have hleft_mem : l.getD i b ∈ l :=
    list_getD_mem_of_lt (l := l) (fallback := b) hi0
  rcases (mem_commonRefinementPointList_iff P Q).1 hleft_mem with hP | hQ
  · rcases (mem_partitionPointSet_iff P).1 hP with ⟨k, hkleft⟩
    have hle :=
      commonRefinementPointList_adjacent_length_le_mesh_of_left_partition
        P Q k hi hkleft.symm
    exact lt_of_le_of_lt hle hPmesh
  · rcases (mem_partitionPointSet_iff Q).1 hQ with ⟨k, hkleft⟩
    have hle :=
      commonRefinementPointList_adjacent_length_le_mesh_of_right_partition
        P Q k hi hkleft.symm
    exact lt_of_le_of_lt hle hQmesh


def DarbouxPartitionRefines {a b : ℝ}
    (R P : Partition a b) : Prop :=
  ∀ i : Fin (P.n + 1), ∃ j : Fin (R.n + 1), R.pts j = P.pts i
noncomputable def DarbouxPartitionRefines.index {a b : ℝ}
    {R P : Partition a b} (href : DarbouxPartitionRefines R P)
    (i : Fin (P.n + 1)) : Fin (R.n + 1) :=
  Classical.choose (href i)
noncomputable def DarbouxPartitionRefines.indexD {a b : ℝ}
    {R P : Partition a b} (href : DarbouxPartitionRefines R P)
    (i : ℕ) : ℕ :=
  if hi : i ≤ P.n then (href.index ⟨i, Nat.lt_succ_iff.mpr hi⟩).val
  else (href.index (Fin.last P.n)).val
lemma DarbouxPartitionRefines.index_le {a b : ℝ}
    {R P : Partition a b} (href : DarbouxPartitionRefines R P)
    (i : Fin (P.n + 1)) :
    (href.index i).val ≤ R.n :=
  Fin.le_last (href.index i)
lemma DarbouxPartitionRefines.index_pts {a b : ℝ}
    {R P : Partition a b} (href : DarbouxPartitionRefines R P)
    (i : Fin (P.n + 1)) :
    R.pts (href.index i) = P.pts i :=
  Classical.choose_spec (href i)
lemma DarbouxPartitionRefines.indexD_eq_index {a b : ℝ}
    {R P : Partition a b} (href : DarbouxPartitionRefines R P)
    {i : ℕ} (hi : i ≤ P.n) :
    href.indexD i = (href.index ⟨i, Nat.lt_succ_iff.mpr hi⟩).val := by
  simp [DarbouxPartitionRefines.indexD, hi]
lemma partition_pts_strict_mono_core {a b : ℝ}
    (P : Partition a b) {i j : Fin (P.n + 1)}
    (hij : i < j) :
    P.pts i < P.pts j := by
  exact P.strict_mono hij
lemma DarbouxPartitionRefines.index_strictMono {a b : ℝ}
    {R P : Partition a b} (href : DarbouxPartitionRefines R P)
    {i j : Fin (P.n + 1)} (hij : i < j) :
    href.index i < href.index j := by
  have hPi_lt_Pj : P.pts i < P.pts j := P.strict_mono hij
  by_contra hnot
  have hRle : R.pts (href.index j) ≤ R.pts (href.index i) :=
    R.strict_mono.monotone (le_of_not_gt hnot)
  rw [DarbouxPartitionRefines.index_pts href j,
    DarbouxPartitionRefines.index_pts href i] at hRle
  exact (not_le_of_gt hPi_lt_Pj) hRle
lemma DarbouxPartitionRefines.index_mono {a b : ℝ}
    {R P : Partition a b} (href : DarbouxPartitionRefines R P)
    {i j : Fin (P.n + 1)} (hij : i ≤ j) :
    href.index i ≤ href.index j := by
  rcases eq_or_lt_of_le hij with rfl | hij_lt
  · rfl
  · exact le_of_lt (DarbouxPartitionRefines.index_strictMono href hij_lt)
lemma partition_node_index_unique {a b : ℝ}
    (P : Partition a b) {i j : Fin (P.n + 1)}
    (hpts : P.pts i = P.pts j) :
    i = j := by
  exact P.strict_mono.injective hpts
lemma DarbouxPartitionRefines.index_zero {a b : ℝ}
    {R P : Partition a b} (href : DarbouxPartitionRefines R P) :
    href.index 0 = 0 := by
  apply partition_node_index_unique R
  rw [DarbouxPartitionRefines.index_pts href 0,
    P.pts_start, R.pts_start]
lemma DarbouxPartitionRefines.index_last {a b : ℝ}
    {R P : Partition a b} (href : DarbouxPartitionRefines R P) :
    href.index (Fin.last P.n) = Fin.last R.n := by
  apply partition_node_index_unique R
  rw [DarbouxPartitionRefines.index_pts href (Fin.last P.n), P.pts_end, R.pts_end]
lemma DarbouxPartitionRefines.subinterval_subset_of_index_block {a b : ℝ}
    {R P : Partition a b} (href : DarbouxPartitionRefines R P)
    {i : Fin P.n} {k : Fin R.n}
    (hk_left : href.index i.castSucc ≤ k.castSucc)
    (hk_right : k.succ ≤ href.index i.succ) :
    Partition.subinterval R k ⊆ Partition.subinterval P i := by
  intro x hx
  unfold Partition.subinterval at hx ⊢
  have hleft_le : P.pts i.castSucc ≤ R.pts k.castSucc := by
    calc
      P.pts i.castSucc = R.pts (href.index i.castSucc) :=
        (DarbouxPartitionRefines.index_pts href i.castSucc).symm
      _ ≤ R.pts k.castSucc := DarbouxRS.partition_pts_monotone_core R hk_left
  have hright_le : R.pts k.succ ≤ P.pts i.succ := by
    calc
      R.pts k.succ ≤ R.pts (href.index i.succ) :=
        DarbouxRS.partition_pts_monotone_core R hk_right
      _ = P.pts i.succ := DarbouxPartitionRefines.index_pts href i.succ
  exact ⟨le_trans hleft_le hx.1, le_trans hx.2 hright_le⟩
lemma partition_subinterval_image_nonempty {a b : ℝ}
    (P : Partition a b) (f : ℝ → ℝ) (i : Fin P.n) :
    (f '' Partition.subinterval P i).Nonempty := by
  refine ⟨f (P.pts i.castSucc), ?_⟩
  refine ⟨P.pts i.castSucc, ?_, rfl⟩
  unfold Partition.subinterval
  exact ⟨le_rfl, le_of_lt (P.strict_mono Fin.castSucc_lt_succ)⟩
lemma lowerStep_le_lowerStep_of_subinterval_subset {f : ℝ → ℝ} {a b : ℝ}
    (P R : Partition a b) {i : Fin P.n} {k : Fin R.n}
    (hBelow : BddBelow (f '' Icc a b))
    (hsub : Partition.subinterval R k ⊆ Partition.subinterval P i) :
    lowerStep P f i ≤ lowerStep R f k := by
  have hPBelow : BddBelow (f '' Partition.subinterval P i) :=
    BddBelow.mono (Set.image_mono (DarbouxRS.subinterval_subset_Icc_core P)) hBelow
  have hRnonempty : (f '' Partition.subinterval R k).Nonempty :=
    partition_subinterval_image_nonempty R f k
  unfold lowerStep
  exact csInf_le_csInf hPBelow hRnonempty (Set.image_mono hsub)
lemma upperStep_le_upperStep_of_subinterval_subset {f : ℝ → ℝ} {a b : ℝ}
    (P R : Partition a b) {i : Fin P.n} {k : Fin R.n}
    (hAbove : BddAbove (f '' Icc a b))
    (hsub : Partition.subinterval R k ⊆ Partition.subinterval P i) :
    upperStep R f k ≤ upperStep P f i := by
  have hPAbove : BddAbove (f '' Partition.subinterval P i) :=
    BddAbove.mono (Set.image_mono (DarbouxRS.subinterval_subset_Icc_core P)) hAbove
  have hRnonempty : (f '' Partition.subinterval R k).Nonempty :=
    partition_subinterval_image_nonempty R f k
  unfold upperStep
  exact csSup_le_csSup hPAbove hRnonempty (Set.image_mono hsub)
private def pointAtNat {a b : ℝ} (P : Partition a b) (j : ℕ) : ℝ :=
  if h : j ≤ P.n then P.pts ⟨j, Nat.lt_succ_iff.mpr h⟩ else b
private lemma pointAtNat_eq {a b : ℝ} (P : Partition a b)
    {j : ℕ} (hj : j ≤ P.n) :
    pointAtNat P j = P.pts ⟨j, Nat.lt_succ_iff.mpr hj⟩ := by
  simp [pointAtNat, hj]
private def lowerTermAtNat {a b : ℝ} (P : Partition a b)
    (f α : ℝ → ℝ) (i : ℕ) : ℝ :=
  if h : i < P.n then
    let iFin : Fin P.n := ⟨i, h⟩
    lowerStep P f iFin *
      (α (P.pts iFin.succ) - α (P.pts iFin.castSucc))
  else 0
private def upperTermAtNat {a b : ℝ} (P : Partition a b)
    (f α : ℝ → ℝ) (i : ℕ) : ℝ :=
  if h : i < P.n then
    let iFin : Fin P.n := ⟨i, h⟩
    upperStep P f iFin *
      (α (P.pts iFin.succ) - α (P.pts iFin.castSucc))
  else 0
private lemma lowerTermAtNat_eq {a b : ℝ} (P : Partition a b)
    (f α : ℝ → ℝ) {i : ℕ} (hi : i < P.n) :
    lowerTermAtNat P f α i =
      lowerStep P f (⟨i, hi⟩ : Fin P.n) *
        (α (P.pts (⟨i, hi⟩ : Fin P.n).succ) -
          α (P.pts (⟨i, hi⟩ : Fin P.n).castSucc)) := by
  simp [lowerTermAtNat, hi]
private lemma upperTermAtNat_eq {a b : ℝ} (P : Partition a b)
    (f α : ℝ → ℝ) {i : ℕ} (hi : i < P.n) :
    upperTermAtNat P f α i =
      upperStep P f (⟨i, hi⟩ : Fin P.n) *
        (α (P.pts (⟨i, hi⟩ : Fin P.n).succ) -
          α (P.pts (⟨i, hi⟩ : Fin P.n).castSucc)) := by
  simp [upperTermAtNat, hi]
private lemma lowerSum_eq_sum_lowerTermAtNat_range {a b : ℝ}
    (P : Partition a b) (f α : ℝ → ℝ) :
    lowerSum P f α =
      ∑ i ∈ Finset.range P.n, lowerTermAtNat P f α i := by
  unfold lowerSum
  calc
    (∑ i : Fin P.n,
        lowerStep P f i *
          (α (P.pts i.succ) - α (P.pts i.castSucc))) =
        ∑ i : Fin P.n, lowerTermAtNat P f α i.val := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [lowerTermAtNat_eq P f α i.isLt]
    _ = ∑ i ∈ Finset.range P.n, lowerTermAtNat P f α i :=
      Fin.sum_univ_eq_sum_range (lowerTermAtNat P f α) P.n
private lemma upperSum_eq_sum_upperTermAtNat_range {a b : ℝ}
    (P : Partition a b) (f α : ℝ → ℝ) :
    upperSum P f α =
      ∑ i ∈ Finset.range P.n, upperTermAtNat P f α i := by
  unfold upperSum
  calc
    (∑ i : Fin P.n,
        upperStep P f i *
          (α (P.pts i.succ) - α (P.pts i.castSucc))) =
        ∑ i : Fin P.n, upperTermAtNat P f α i.val := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [upperTermAtNat_eq P f α i.isLt]
    _ = ∑ i ∈ Finset.range P.n, upperTermAtNat P f α i :=
      Fin.sum_univ_eq_sum_range (upperTermAtNat P f α) P.n
lemma sum_Ico_refinement_blocks_eq_Ico {β : Type*} [AddCommMonoid β]
    (g : ℕ → β) (idx : ℕ → ℕ) :
    ∀ n : ℕ,
      (∀ i, i < n → idx i ≤ idx (i + 1)) →
        (∑ i ∈ Finset.range n,
            ∑ k ∈ Finset.Ico (idx i) (idx (i + 1)), g k) =
          ∑ k ∈ Finset.Ico (idx 0) (idx n), g k := by
  intro n
  induction n with
  | zero =>
      intro _hmono
      simp
  | succ n ih =>
      intro hmono
      rw [Finset.sum_range_succ]
      have hmono_init : ∀ i, i < n → idx i ≤ idx (i + 1) := by
        intro i hi
        exact hmono i (Nat.lt_trans hi (Nat.lt_succ_self n))
      rw [ih hmono_init]
      have h0n : idx 0 ≤ idx n := by
        have hchain :
            ∀ m : ℕ, (∀ i, i < m → idx i ≤ idx (i + 1)) → idx 0 ≤ idx m := by
          intro m
          induction m with
          | zero =>
              intro _hm
              rfl
          | succ m ihm =>
              intro hm
              have hm_init : ∀ i, i < m → idx i ≤ idx (i + 1) := by
                intro i hi
                exact hm i (Nat.lt_trans hi (Nat.lt_succ_self m))
              exact le_trans (ihm hm_init) (hm m (Nat.lt_succ_self m))
        exact hchain n hmono_init
      have hn : idx n ≤ idx (n + 1) := hmono n (Nat.lt_succ_self n)
      rw [Finset.sum_Ico_consecutive g h0n hn]
lemma sum_Ico_refinement_blocks_eq_range {a b : ℝ}
    {R P : Partition a b} (href : DarbouxPartitionRefines R P)
    (g : ℕ → ℝ) :
    (∑ i ∈ Finset.range P.n,
        ∑ k ∈ Finset.Ico
          (href.indexD i)
          (href.indexD (i + 1)), g k) =
      ∑ k ∈ Finset.range R.n, g k := by
  let idx : ℕ → ℕ := href.indexD
  have hmono : ∀ i, i < P.n → idx i ≤ idx (i + 1) := by
    intro i hi
    have hi_le : i ≤ P.n := Nat.le_of_lt hi
    have hi1_le : i + 1 ≤ P.n := Nat.succ_le_of_lt hi
    simp [idx, DarbouxPartitionRefines.indexD_eq_index href hi_le,
      DarbouxPartitionRefines.indexD_eq_index href hi1_le]
    exact le_of_lt (DarbouxPartitionRefines.index_strictMono href (by
      change i < i + 1
      omega))
  have hblocks := sum_Ico_refinement_blocks_eq_Ico g idx P.n hmono
  have hidx0 : idx 0 = 0 := by
    have h0 : 0 ≤ P.n := Nat.zero_le P.n
    simp [idx, DarbouxPartitionRefines.indexD_eq_index href h0,
      DarbouxPartitionRefines.index_zero href]
  have hidxn : idx P.n = R.n := by
    rw [show idx P.n = (href.index (Fin.last P.n)).val by
      exact DarbouxPartitionRefines.indexD_eq_index href le_rfl]
    rw [DarbouxPartitionRefines.index_last href]
    rfl
  simpa [idx, hidx0, hidxn] using hblocks
private lemma DarbouxPartitionRefines.lower_cell_le_block_sum
    {f α : ℝ → ℝ} {a b : ℝ}
    (hs : SourceHypotheses a b f α)
    {R P : Partition a b} (href : DarbouxPartitionRefines R P)
    (i : Fin P.n) :
    lowerStep P f i *
        (α (P.pts i.succ) - α (P.pts i.castSucc)) ≤
      ∑ k ∈ Finset.Ico
          (href.index i.castSucc).val
          (href.index i.succ).val,
        lowerTermAtNat R f α k := by
  rcases hs with ⟨hab, hAbove, hBelow, hmonoα⟩
  let j0 := (href.index i.castSucc).val
  let j1 := (href.index i.succ).val
  have hj0j1 : j0 ≤ j1 := le_of_lt
    (DarbouxPartitionRefines.index_strictMono href Fin.castSucc_lt_succ)
  have hj1_le : j1 ≤ R.n := DarbouxPartitionRefines.index_le href i.succ
  have htel :
      (∑ k ∈ Finset.Ico j0 j1,
          (α (pointAtNat R (k + 1)) - α (pointAtNat R k))) =
        α (pointAtNat R j1) - α (pointAtNat R j0) := by
    exact Finset.sum_Ico_sub (fun k => α (pointAtNat R k)) hj0j1
  calc
    lowerStep P f i *
        (α (P.pts i.succ) - α (P.pts i.castSucc))
        = lowerStep P f i *
          (α (pointAtNat R j1) - α (pointAtNat R j0)) := by
            rw [pointAtNat_eq R hj1_le,
              pointAtNat_eq R (DarbouxPartitionRefines.index_le href i.castSucc)]
            rw [DarbouxPartitionRefines.index_pts href i.succ,
              DarbouxPartitionRefines.index_pts href i.castSucc]
    _ = lowerStep P f i *
          (∑ k ∈ Finset.Ico j0 j1,
            (α (pointAtNat R (k + 1)) - α (pointAtNat R k))) := by rw [htel]
    _ = ∑ k ∈ Finset.Ico j0 j1,
          lowerStep P f i *
            (α (pointAtNat R (k + 1)) - α (pointAtNat R k)) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ k ∈ Finset.Ico j0 j1,
          lowerTermAtNat R f α k := by
        refine Finset.sum_le_sum ?_
        intro k hk_mem
        have hkI := Finset.mem_Ico.mp hk_mem
        have hk_lt_j1 : k < j1 := hkI.2
        have hk_left : j0 ≤ k := hkI.1
        have hk_right : k + 1 ≤ j1 := Nat.succ_le_of_lt hk_lt_j1
        have hk_lt_Rn : k < R.n := lt_of_lt_of_le hk_lt_j1 hj1_le
        let kFin : Fin R.n := ⟨k, hk_lt_Rn⟩
        have hsub :
            Partition.subinterval R kFin ⊆ Partition.subinterval P i := by
          apply DarbouxPartitionRefines.subinterval_subset_of_index_block href
          · exact_mod_cast hk_left
          · exact_mod_cast hk_right
        have hstep :
            lowerStep P f i ≤ lowerStep R f kFin :=
          lowerStep_le_lowerStep_of_subinterval_subset P R hBelow hsub
        have hinc :
            0 ≤ α (R.pts kFin.succ) - α (R.pts kFin.castSucc) :=
          DarbouxRS.partition_increment_nonneg_of_source_core_local R
            ⟨hab, hAbove, hBelow, hmonoα⟩
        rw [lowerTermAtNat_eq R f α hk_lt_Rn,
          pointAtNat_eq R (Nat.succ_le_of_lt hk_lt_Rn),
          pointAtNat_eq R (Nat.le_of_lt hk_lt_Rn)]
        exact mul_le_mul_of_nonneg_right hstep hinc
private lemma DarbouxPartitionRefines.upper_block_sum_le_cell
    {f α : ℝ → ℝ} {a b : ℝ}
    (hs : SourceHypotheses a b f α)
    {R P : Partition a b} (href : DarbouxPartitionRefines R P)
    (i : Fin P.n) :
      (∑ k ∈ Finset.Ico
          (href.index i.castSucc).val
          (href.index i.succ).val,
        upperTermAtNat R f α k) ≤
      upperStep P f i *
        (α (P.pts i.succ) - α (P.pts i.castSucc)) := by
  rcases hs with ⟨hab, hAbove, hBelow, hmonoα⟩
  let j0 := (href.index i.castSucc).val
  let j1 := (href.index i.succ).val
  have hj0j1 : j0 ≤ j1 := le_of_lt
    (DarbouxPartitionRefines.index_strictMono href Fin.castSucc_lt_succ)
  have hj1_le : j1 ≤ R.n := DarbouxPartitionRefines.index_le href i.succ
  have htel :
      (∑ k ∈ Finset.Ico j0 j1,
          (α (pointAtNat R (k + 1)) - α (pointAtNat R k))) =
        α (pointAtNat R j1) - α (pointAtNat R j0) := by
    exact Finset.sum_Ico_sub (fun k => α (pointAtNat R k)) hj0j1
  calc
    (∑ k ∈ Finset.Ico j0 j1,
        upperTermAtNat R f α k)
        ≤ ∑ k ∈ Finset.Ico j0 j1,
          upperStep P f i *
            (α (pointAtNat R (k + 1)) - α (pointAtNat R k)) := by
          refine Finset.sum_le_sum ?_
          intro k hk_mem
          have hkI := Finset.mem_Ico.mp hk_mem
          have hk_lt_j1 : k < j1 := hkI.2
          have hk_left : j0 ≤ k := hkI.1
          have hk_right : k + 1 ≤ j1 := Nat.succ_le_of_lt hk_lt_j1
          have hk_lt_Rn : k < R.n := lt_of_lt_of_le hk_lt_j1 hj1_le
          let kFin : Fin R.n := ⟨k, hk_lt_Rn⟩
          have hsub :
              Partition.subinterval R kFin ⊆ Partition.subinterval P i := by
            apply DarbouxPartitionRefines.subinterval_subset_of_index_block href
            · exact_mod_cast hk_left
            · exact_mod_cast hk_right
          have hstep :
              upperStep R f kFin ≤ upperStep P f i :=
            upperStep_le_upperStep_of_subinterval_subset P R hAbove hsub
          have hinc :
              0 ≤ α (R.pts kFin.succ) - α (R.pts kFin.castSucc) :=
            DarbouxRS.partition_increment_nonneg_of_source_core_local R
              ⟨hab, hAbove, hBelow, hmonoα⟩
          rw [upperTermAtNat_eq R f α hk_lt_Rn,
            pointAtNat_eq R (Nat.succ_le_of_lt hk_lt_Rn),
            pointAtNat_eq R (Nat.le_of_lt hk_lt_Rn)]
          exact mul_le_mul_of_nonneg_right hstep hinc
    _ = upperStep P f i *
          (∑ k ∈ Finset.Ico j0 j1,
            (α (pointAtNat R (k + 1)) - α (pointAtNat R k))) := by
        rw [Finset.mul_sum]
    _ = upperStep P f i *
          (α (pointAtNat R j1) - α (pointAtNat R j0)) := by rw [htel]
    _ = upperStep P f i *
        (α (P.pts i.succ) - α (P.pts i.castSucc)) := by
          rw [pointAtNat_eq R hj1_le,
            pointAtNat_eq R (DarbouxPartitionRefines.index_le href i.castSucc)]
          rw [DarbouxPartitionRefines.index_pts href i.succ,
            DarbouxPartitionRefines.index_pts href i.castSucc]
lemma DarbouxPartitionRefines_of_partitionOfStrictEndpointList {a b : ℝ}
    (P : Partition a b) (l : List ℝ)
    (hlen : 2 ≤ l.length)
    (hstart : l.getD 0 b = a)
    (hend : l.getD (l.length - 1) a = b)
    (hstrict : ∀ {i : ℕ}, i + 1 < l.length → l.getD i b < l.getD (i + 1) b)
    (hcover : ∀ i : Fin (P.n + 1), P.pts i ∈ l) :
    DarbouxPartitionRefines
      (partitionOfStrictEndpointList l hlen hstart hend hstrict) P := by
  intro i
  exact partitionOfStrictEndpointList_mem_node_local l hlen hstart hend hstrict (hcover i)
lemma concreteCommonRefinementPartition_refines_left {a b : ℝ}
    (P Q : Partition a b) :
    DarbouxPartitionRefines (concreteCommonRefinementPartition P Q) P := by
  unfold concreteCommonRefinementPartition
  exact DarbouxPartitionRefines_of_partitionOfStrictEndpointList
    P (commonRefinementPointList P Q)
    (commonRefinementPointList_length_two_le P Q)
    (commonRefinementPointList_getD_zero P Q)
    (commonRefinementPointList_getD_last P Q)
    (fun hi => commonRefinementPointList_adjacent_getD_lt P Q hi)
    (fun i => commonRefinementPointList_covers_left P Q i)
lemma concreteCommonRefinementPartition_refines_right {a b : ℝ}
    (P Q : Partition a b) :
    DarbouxPartitionRefines (concreteCommonRefinementPartition P Q) Q := by
  unfold concreteCommonRefinementPartition
  exact DarbouxPartitionRefines_of_partitionOfStrictEndpointList
    Q (commonRefinementPointList P Q)
    (commonRefinementPointList_length_two_le P Q)
    (commonRefinementPointList_getD_zero P Q)
    (commonRefinementPointList_getD_last P Q)
    (fun hi => commonRefinementPointList_adjacent_getD_lt P Q hi)
    (fun i => commonRefinementPointList_covers_right P Q i)
theorem DarbouxCommonRefinementExists_nodes {a b : ℝ}
    (P Q : Partition a b) :
    ∃ R : Partition a b,
      DarbouxPartitionRefines R P ∧ DarbouxPartitionRefines R Q := by
  refine ⟨concreteCommonRefinementPartition P Q, ?_, ?_⟩
  · exact concreteCommonRefinementPartition_refines_left P Q
  · exact concreteCommonRefinementPartition_refines_right P Q
lemma concreteCommonRefinementPartition_mesh_lt {a b δ : ℝ}
    (P Q : Partition a b)
    (hPmesh : P.mesh < δ) (hQmesh : Q.mesh < δ) :
    (concreteCommonRefinementPartition P Q).mesh < δ := by
  unfold concreteCommonRefinementPartition partitionOfStrictEndpointList
    Partition.mesh
  refine (Finset.sup'_lt_iff _).2 ?_
  intro i _hi
  exact commonRefinementPointList_adjacent_length_lt_delta_local
    P Q hPmesh hQmesh (by
      have hi' : i < (commonRefinementPointList P Q).length - 1 :=
        i.isLt
      omega)

def DarbouxCommonRefinementExists (a b : ℝ) : Prop :=
  ∀ δ > 0, ∀ P Q : Partition a b,
    P.mesh < δ →
    Q.mesh < δ →
      ∃ R : Partition a b,
        R.mesh < δ ∧
        DarbouxPartitionRefines R P ∧
        DarbouxPartitionRefines R Q
theorem DarbouxCommonRefinementExists_concrete {a b : ℝ} :
    DarbouxCommonRefinementExists a b := by
  intro δ _hδ P Q hPmesh hQmesh
  refine ⟨concreteCommonRefinementPartition P Q, ?_, ?_, ?_⟩
  · exact concreteCommonRefinementPartition_mesh_lt P Q hPmesh hQmesh
  · exact concreteCommonRefinementPartition_refines_left P Q
  · exact concreteCommonRefinementPartition_refines_right P Q

def DarbouxRefinementSumMonotone
    (a b : ℝ) (f α : ℝ → ℝ) : Prop :=
  SourceHypotheses a b f α →
    ∀ P R : Partition a b,
      DarbouxPartitionRefines R P →
        lowerSum P f α ≤ lowerSum R f α ∧
        upperSum R f α ≤ upperSum P f α
end Thm11SourceRoute


