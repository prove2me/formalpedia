-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F007
-- name    : ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F007
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T23:13:50.925449+00:00
-- url     : https://prove2.me/theorems/3b97dd9a-b87a-4c84-9d1d-7ad34e748c1f
-- title:
--   Chapter 1, thm_1_1_bad_cells: supporting Lean bundle F007
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_1_bad_cells`: `pointAtNat`, `pointAtNat_eq`, `pointAtNat_zero`, `pointAtNat_end`, `pointAtNat_mono`, and 4 others. The mathematical interpretation of this bundle needs review.
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

private lemma partition_increment_sum_Ico_le_bad_interval
    {α : ℝ → ℝ} {a b c r : ℝ}
    (hα_mono : Monotone α)
    (P : Partition a b) {j0 j1 : ℕ}
    (hj0j1 : j0 ≤ j1)
    (_hj1 : j1 ≤ P.n)
    (hleft : c - r ≤ pointAtNat P j0)
    (hright : pointAtNat P j1 ≤ c + r) :
    (∑ i ∈ Finset.Ico j0 j1,
        (α (pointAtNat P (i + 1)) - α (pointAtNat P i))) ≤
      α (c + r) - α (c - r) := by
  have htel :
      (∑ i ∈ Finset.Ico j0 j1,
          (α (pointAtNat P (i + 1)) - α (pointAtNat P i))) =
        α (pointAtNat P j1) - α (pointAtNat P j0) := by
    exact Finset.sum_Ico_sub (fun k => α (pointAtNat P k)) hj0j1
  have hα_left : α (c - r) ≤ α (pointAtNat P j0) := hα_mono hleft
  have hα_right : α (pointAtNat P j1) ≤ α (c + r) := hα_mono hright
  rw [htel]
  linarith

private lemma partition_increment_sum_Ico_blocks_le_bad_intervals
    {α : ℝ → ℝ} {a b : ℝ}
    (hα_mono : Monotone α)
    (P : Partition a b)
    (S : Finset ℝ) (rho : ℝ → ℝ) (lo hi : ℝ → ℕ)
    (hlohi : ∀ c : ℝ, c ∈ S → lo c ≤ hi c)
    (hhi : ∀ c : ℝ, c ∈ S → hi c ≤ P.n)
    (hleft : ∀ c : ℝ, c ∈ S → c - rho c ≤ pointAtNat P (lo c))
    (hright : ∀ c : ℝ, c ∈ S → pointAtNat P (hi c) ≤ c + rho c) :
    (∑ c ∈ S,
        ∑ i ∈ Finset.Ico (lo c) (hi c),
          (α (pointAtNat P (i + 1)) - α (pointAtNat P i))) ≤
      ∑ c ∈ S, (α (c + rho c) - α (c - rho c)) := by
  refine Finset.sum_le_sum ?_
  intro c hc
  exact partition_increment_sum_Ico_le_bad_interval hα_mono P
    (hlohi c hc) (hhi c hc) (hleft c hc) (hright c hc)

private lemma partition_increment_sum_le_bad_intervals_of_disjoint_Ico_cover
    {α : ℝ → ℝ} {a b : ℝ}
    (hα_mono : Monotone α)
    (P : Partition a b)
    (B : Finset ℕ) (S : Finset ℝ) (rho : ℝ → ℝ) (lo hi : ℝ → ℕ)
    (hdisj :
      (↑S : Set ℝ).PairwiseDisjoint
        (fun c : ℝ => Finset.Ico (lo c) (hi c)))
    (hcover :
      B ⊆ S.biUnion (fun c : ℝ => Finset.Ico (lo c) (hi c)))
    (hlohi : ∀ c : ℝ, c ∈ S → lo c ≤ hi c)
    (hhi : ∀ c : ℝ, c ∈ S → hi c ≤ P.n)
    (hleft : ∀ c : ℝ, c ∈ S → c - rho c ≤ pointAtNat P (lo c))
    (hright : ∀ c : ℝ, c ∈ S → pointAtNat P (hi c) ≤ c + rho c) :
    (∑ i ∈ B, (α (pointAtNat P (i + 1)) - α (pointAtNat P i))) ≤
      ∑ c ∈ S, (α (c + rho c) - α (c - rho c)) := by
  let blockUnion : Finset ℕ :=
    S.biUnion (fun c : ℝ => Finset.Ico (lo c) (hi c))
  let inc : ℕ → ℝ := fun i => α (pointAtNat P (i + 1)) - α (pointAtNat P i)
  have hB_le_union :
      (∑ i ∈ B, inc i) ≤ ∑ i ∈ blockUnion, inc i := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hcover ?_
    intro i hi_union _hi_not_B
    rcases (Finset.mem_biUnion.mp hi_union) with ⟨c, hcS, hiIco⟩
    have hi_lt : i < P.n := by
      have hi_block := (Finset.mem_Ico.mp hiIco).2
      exact lt_of_lt_of_le hi_block (hhi c hcS)
    have hpts : pointAtNat P i ≤ pointAtNat P (i + 1) :=
      pointAtNat_mono P (Nat.le_of_lt hi_lt) (Nat.succ_le_of_lt hi_lt) (by omega)
    have hα : α (pointAtNat P i) ≤ α (pointAtNat P (i + 1)) := hα_mono hpts
    dsimp [inc]
    linarith
  have hunion_eq :
      (∑ i ∈ blockUnion, inc i) =
        ∑ c ∈ S, ∑ i ∈ Finset.Ico (lo c) (hi c), inc i := by
    dsimp [blockUnion]
    exact Finset.sum_biUnion hdisj
  have hblocks_le :
      (∑ c ∈ S,
          ∑ i ∈ Finset.Ico (lo c) (hi c),
            (α (pointAtNat P (i + 1)) - α (pointAtNat P i))) ≤
        ∑ c ∈ S, (α (c + rho c) - α (c - rho c)) :=
    partition_increment_sum_Ico_blocks_le_bad_intervals hα_mono P S rho lo hi
      hlohi hhi hleft hright
  calc
    (∑ i ∈ B, (α (pointAtNat P (i + 1)) - α (pointAtNat P i)))
        = ∑ i ∈ B, inc i := by rfl
    _ ≤ ∑ i ∈ blockUnion, inc i := hB_le_union
    _ = ∑ c ∈ S, ∑ i ∈ Finset.Ico (lo c) (hi c), inc i := hunion_eq
    _ = ∑ c ∈ S,
          ∑ i ∈ Finset.Ico (lo c) (hi c),
            (α (pointAtNat P (i + 1)) - α (pointAtNat P i)) := by rfl
    _ ≤ ∑ c ∈ S, (α (c + rho c) - α (c - rho c)) := hblocks_le
end Thm11SourceRoute


