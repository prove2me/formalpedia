-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F006
-- name    : ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F006
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T23:44:13.076464+00:00
-- url     : https://prove2.me/theorems/07f83613-a355-4670-92e8-fddf4eb36eda
-- title:
--   Chapter 1, thm_1_1_bad_cells: supporting Lean bundle F006
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_1_bad_cells`: `pointAtNat`, `pointAtNat_eq`, `pointAtNat_zero`, `pointAtNat_end`, `pointAtNat_mono`, and 18 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_bad_cells.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F005
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute

private def pointAtNat {a b : ℝ} (P : Partition a b) (j : ℕ) : ℝ :=
  if h : j ≤ P.n then P.pts ⟨j, Nat.lt_succ_iff.mpr h⟩ else b
private lemma pointAtNat_eq {a b : ℝ} (P : Partition a b)
    {j : ℕ} (hj : j ≤ P.n) :
    pointAtNat P j = P.pts ⟨j, Nat.lt_succ_iff.mpr hj⟩ := by
  simp [pointAtNat, hj]
private lemma pointAtNat_zero {a b : ℝ} (P : Partition a b) :
    pointAtNat P 0 = a := by
  simp [pointAtNat, P.pts_start]
private lemma pointAtNat_end {a b : ℝ} (P : Partition a b) :
    pointAtNat P P.n = b := by
  rw [pointAtNat_eq P (le_refl P.n)]
  convert P.pts_end using 1
  congr 1
private lemma pointAtNat_mono {a b : ℝ} (P : Partition a b)
    {i j : ℕ} (hi : i ≤ P.n) (hj : j ≤ P.n) (hij : i ≤ j) :
    pointAtNat P i ≤ pointAtNat P j := by
  rw [pointAtNat_eq P hi, pointAtNat_eq P hj]
  exact DarbouxRS.partition_pts_monotone_core P (by exact_mod_cast hij)
private lemma pointAtNat_strictMono {a b : ℝ} (P : Partition a b)
    {i j : ℕ} (hi : i ≤ P.n) (hj : j ≤ P.n) (hij : i < j) :
    pointAtNat P i < pointAtNat P j := by
  rw [pointAtNat_eq P hi, pointAtNat_eq P hj]
  exact P.strict_mono (by exact_mod_cast hij)

private lemma mem_badPointEndpointBlock_iff {a b c r : ℝ}
    (P : Partition a b) {i : ℕ} :
    i ∈ badPointEndpointBlock P c r ↔
      i < P.n ∧ c - r < pointAtNat P i ∧ pointAtNat P (i + 1) < c + r := by
  classical
  simp only [badPointEndpointBlock, Finset.mem_filter, Finset.mem_range] <;> rfl
/-- Disjoint real bad-point intervals induce disjoint endpoint-cell blocks. -/
private lemma badPointEndpointBlock_disjoint_of_disjoint_Ioo_source_local {a b c d r s : ℝ}
    (P : Partition a b)
    (hsep :
      Disjoint (Set.Ioo (c - r) (c + r)) (Set.Ioo (d - s) (d + s))) :
    Disjoint (badPointEndpointBlock P c r) (badPointEndpointBlock P d s) := by
  classical
  rw [Finset.disjoint_left]
  intro i hiC hiD
  rw [mem_badPointEndpointBlock_iff P] at hiC
  rw [mem_badPointEndpointBlock_iff P] at hiD
  have hstep : pointAtNat P i < pointAtNat P (i + 1) :=
    pointAtNat_strictMono P (Nat.le_of_lt hiC.1) (Nat.succ_le_of_lt hiC.1) (by omega)
  have hxC : pointAtNat P i ∈ Set.Ioo (c - r) (c + r) :=
    ⟨hiC.2.1, lt_trans hstep hiC.2.2⟩
  have hxD : pointAtNat P i ∈ Set.Ioo (d - s) (d + s) :=
    ⟨hiD.2.1, lt_trans hstep hiD.2.2⟩
  have hempty :
      Set.Ioo (c - r) (c + r) ∩ Set.Ioo (d - s) (d + s) = (∅ : Set ℝ) :=
    Set.disjoint_iff_inter_eq_empty.mp hsep
  have hxempty : pointAtNat P i ∈ (∅ : Set ℝ) := by
    simpa [hempty] using
      (show pointAtNat P i ∈
          Set.Ioo (c - r) (c + r) ∩ Set.Ioo (d - s) (d + s) from
        ⟨hxC, hxD⟩)
  exact hxempty

lemma badPointEndpointBlocks_pairwiseDisjoint_of_pairwiseDisjoint_Ioo
    {a b : ℝ} (P : Partition a b)
    (S : Finset ℝ) (rho : ℝ → ℝ)
    (hsep :
      (↑S : Set ℝ).PairwiseDisjoint
        (fun c : ℝ => Set.Ioo (c - rho c) (c + rho c))) :
    (↑S : Set ℝ).PairwiseDisjoint
      (fun c : ℝ => badPointEndpointBlock P c (rho c)) := by
  classical
  rw [Set.PairwiseDisjoint] at hsep ⊢
  intro c hc d hd hne
  exact badPointEndpointBlock_disjoint_of_disjoint_Ioo_source_local P (hsep hc hd hne)

noncomputable def badPointLeftCutCandidates {a b : ℝ}
    (P : Partition a b) (c r : ℝ) : Finset ℕ :=
  (Finset.range (P.n + 1)).filter (fun j => c - r ≤ pointAtNat P j)

noncomputable def badPointRightCutCandidates {a b : ℝ}
    (P : Partition a b) (c r : ℝ) : Finset ℕ :=
  (Finset.range (P.n + 1)).filter (fun j => pointAtNat P j ≤ c + r)

noncomputable def badPointCanonicalLo {a b : ℝ}
    (P : Partition a b) (c r : ℝ) : ℕ :=
  if h : (badPointLeftCutCandidates P c r).Nonempty then
    (badPointLeftCutCandidates P c r).min' h
  else 0

noncomputable def badPointCanonicalHi {a b : ℝ}
    (P : Partition a b) (c r : ℝ) : ℕ :=
  if h : (badPointRightCutCandidates P c r).Nonempty then
    (badPointRightCutCandidates P c r).max' h
  else 0
lemma badPointLeftCutCandidates_nonempty {a b c r : ℝ}
    (P : Partition a b)
    (hcI : c ∈ Icc a b) (hr : 0 < r) :
    (badPointLeftCutCandidates P c r).Nonempty := by
  refine ⟨P.n, ?_⟩
  simp [badPointLeftCutCandidates, pointAtNat_end P]
  linarith [hcI.2, hr]
lemma badPointRightCutCandidates_nonempty {a b c r : ℝ}
    (P : Partition a b)
    (hcI : c ∈ Icc a b) (hr : 0 < r) :
    (badPointRightCutCandidates P c r).Nonempty := by
  refine ⟨0, ?_⟩
  simp [badPointRightCutCandidates, pointAtNat_zero P]
  linarith [hcI.1, hr]
lemma badPointCanonicalLo_mem_leftCandidates {a b c r : ℝ}
    (P : Partition a b)
    (hcI : c ∈ Icc a b) (hr : 0 < r) :
    badPointCanonicalLo P c r ∈ badPointLeftCutCandidates P c r := by
  have hne := badPointLeftCutCandidates_nonempty P hcI hr
  dsimp [badPointCanonicalLo]
  rw [dif_pos hne]
  exact Finset.min'_mem _ hne
lemma badPointCanonicalHi_mem_rightCandidates {a b c r : ℝ}
    (P : Partition a b)
    (hcI : c ∈ Icc a b) (hr : 0 < r) :
    badPointCanonicalHi P c r ∈ badPointRightCutCandidates P c r := by
  have hne := badPointRightCutCandidates_nonempty P hcI hr
  dsimp [badPointCanonicalHi]
  rw [dif_pos hne]
  exact Finset.max'_mem _ hne
lemma badPointCanonicalLo_le_of_mem_leftCandidates {a b c r : ℝ}
    (P : Partition a b)
    (hcI : c ∈ Icc a b) (hr : 0 < r) {j : ℕ}
    (hj : j ∈ badPointLeftCutCandidates P c r) :
    badPointCanonicalLo P c r ≤ j := by
  have hne := badPointLeftCutCandidates_nonempty P hcI hr
  dsimp [badPointCanonicalLo]
  rw [dif_pos hne]
  exact Finset.min'_le _ j hj
lemma le_badPointCanonicalHi_of_mem_rightCandidates {a b c r : ℝ}
    (P : Partition a b)
    (hcI : c ∈ Icc a b) (hr : 0 < r) {j : ℕ}
    (hj : j ∈ badPointRightCutCandidates P c r) :
    j ≤ badPointCanonicalHi P c r := by
  have hne := badPointRightCutCandidates_nonempty P hcI hr
  dsimp [badPointCanonicalHi]
  rw [dif_pos hne]
  exact Finset.le_max' _ j hj
lemma badPointCanonicalLo_le_n {a b c r : ℝ}
    (P : Partition a b)
    (hcI : c ∈ Icc a b) (hr : 0 < r) :
    badPointCanonicalLo P c r ≤ P.n := by
  have hmem := badPointCanonicalLo_mem_leftCandidates P hcI hr
  rw [badPointLeftCutCandidates] at hmem
  have hrange := (Finset.mem_filter.mp hmem).1
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hrange)
lemma badPointCanonicalHi_le_n {a b c r : ℝ}
    (P : Partition a b)
    (hcI : c ∈ Icc a b) (hr : 0 < r) :
    badPointCanonicalHi P c r ≤ P.n := by
  have hmem := badPointCanonicalHi_mem_rightCandidates P hcI hr
  rw [badPointRightCutCandidates] at hmem
  have hrange := (Finset.mem_filter.mp hmem).1
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hrange)
private lemma badPointCanonicalLo_left_bound {a b c r : ℝ}
    (P : Partition a b)
    (hcI : c ∈ Icc a b) (hr : 0 < r) :
    c - r ≤ pointAtNat P (badPointCanonicalLo P c r) := by
  have hmem := badPointCanonicalLo_mem_leftCandidates P hcI hr
  rw [badPointLeftCutCandidates] at hmem
  exact (Finset.mem_filter.mp hmem).2
private lemma badPointCanonicalHi_right_bound {a b c r : ℝ}
    (P : Partition a b)
    (hcI : c ∈ Icc a b) (hr : 0 < r) :
    pointAtNat P (badPointCanonicalHi P c r) ≤ c + r := by
  have hmem := badPointCanonicalHi_mem_rightCandidates P hcI hr
  rw [badPointRightCutCandidates] at hmem
  exact (Finset.mem_filter.mp hmem).2
private lemma badPointCanonicalLo_right_bound_of_mesh {a b c r : ℝ}
    (P : Partition a b)
    (hcI : c ∈ Icc a b) (hr : 0 < r)
    (hmesh : P.mesh < r / 2) :
    pointAtNat P (badPointCanonicalLo P c r) ≤ c + r := by
  by_cases hlo0 : badPointCanonicalLo P c r = 0
  · rw [hlo0, pointAtNat_zero]
    linarith [hcI.1, hr]
  · let k := badPointCanonicalLo P c r - 1
    have hk_succ : k + 1 = badPointCanonicalLo P c r := by
      dsimp [k]
      omega
    have hk_lt_lo : k < badPointCanonicalLo P c r := by
      dsimp [k]
      omega
    have hlo_le_n := badPointCanonicalLo_le_n P hcI hr
    have hk_lt_n : k < P.n := by
      dsimp [k]
      omega
    have hk_not_mem : k ∉ badPointLeftCutCandidates P c r := by
      intro hk_mem
      have hlo_le_k := badPointCanonicalLo_le_of_mem_leftCandidates P hcI hr hk_mem
      omega
    have hk_left_lt : pointAtNat P k < c - r := by
      apply lt_of_not_ge
      intro hk_left
      apply hk_not_mem
      rw [badPointLeftCutCandidates]
      refine Finset.mem_filter.mpr ⟨?_, hk_left⟩
      exact Finset.mem_range.mpr (Nat.lt_trans hk_lt_n (Nat.lt_succ_self P.n))
    have hlen_mesh : pointAtNat P (k + 1) - pointAtNat P k ≤ P.mesh := by
      unfold Partition.mesh
      rw [pointAtNat_eq P (Nat.succ_le_of_lt hk_lt_n), pointAtNat_eq P (Nat.le_of_lt hk_lt_n)]
      exact Finset.le_sup'
        (fun j : Fin P.n => P.pts j.succ - P.pts j.castSucc)
        (Finset.mem_univ ⟨k, hk_lt_n⟩)
    have hlen_lt : pointAtNat P (badPointCanonicalLo P c r) - pointAtNat P k < r / 2 := by
      have h := lt_of_le_of_lt hlen_mesh hmesh
      simpa [hk_succ] using h
    linarith
lemma badPointCanonicalLo_le_hi_of_mesh {a b c r : ℝ}
    (P : Partition a b)
    (hcI : c ∈ Icc a b) (hr : 0 < r)
    (hmesh : P.mesh < r / 2) :
    badPointCanonicalLo P c r ≤ badPointCanonicalHi P c r := by
  have hlo_le_n := badPointCanonicalLo_le_n P hcI hr
  have hlo_right := badPointCanonicalLo_right_bound_of_mesh P hcI hr hmesh
  have hlo_mem_right : badPointCanonicalLo P c r ∈ badPointRightCutCandidates P c r := by
    rw [badPointRightCutCandidates]
    refine Finset.mem_filter.mpr ⟨?_, hlo_right⟩
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hlo_le_n)
  exact le_badPointCanonicalHi_of_mem_rightCandidates P hcI hr hlo_mem_right
end Thm11SourceRoute


