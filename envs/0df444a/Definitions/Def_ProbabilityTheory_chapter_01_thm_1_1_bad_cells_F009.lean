-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F009
-- name    : ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F009
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-13T00:08:18.032557+00:00
-- url     : https://prove2.me/theorems/504982e3-5df6-46be-8f62-a55a7812fef0
-- title:
--   Chapter 1, thm_1_1_bad_cells: supporting Lean bundle F009
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_1_bad_cells`: `pointAtNat`, `pointAtNat_eq`, `pointAtNat_zero`, `pointAtNat_end`, `pointAtNat_mono`, and 10 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_bad_cells.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F005
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F006
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F007
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F008
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_oscillation_basic_F000
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

/-- The partition indices whose cells are not contained in the chosen good
remainder. These are the cells that must be charged to bad-point neighborhoods. -/
private def subintervalAtNat_local {a b : ℝ} (P : Partition a b) (i : ℕ) : Set ℝ :=
  if h : i < P.n then Partition.subinterval P ⟨i, h⟩ else ∅

private lemma mem_badCellIndices_iff_local {a b : ℝ}
    (P : Partition a b) (S : Finset ℝ) (rho : ℝ → ℝ) {i : ℕ} :
    i ∈ badCellIndices P S rho ↔
      i < P.n ∧
        ∀ hi : i < P.n,
          ¬ Partition.subinterval P ⟨i, hi⟩ ⊆ goodRemainder a b S rho := by
  classical
  rw [badCellIndices, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hi, hbad⟩
    refine ⟨hi, ?_⟩
    intro hi'
    change ¬ subintervalAtNat_local P i ⊆ goodRemainder a b S rho at hbad
    simpa [subintervalAtNat_local, hi'] using hbad
  · rintro ⟨hi, hbad⟩
    refine ⟨hi, ?_⟩
    change ¬ subintervalAtNat_local P i ⊆ goodRemainder a b S rho
    simpa [subintervalAtNat_local, hi] using hbad hi

private lemma cell_subset_goodRemainder_of_not_mem_badCellIndices_local {a b : ℝ}
    (P : Partition a b) (S : Finset ℝ) (rho : ℝ → ℝ)
    (i : Fin P.n)
    (hi_not_bad : i.val ∉ badCellIndices P S rho) :
    Partition.subinterval P i ⊆ goodRemainder a b S rho := by
  by_contra hnot
  exact hi_not_bad ((mem_badCellIndices_iff_local P S rho).2 ⟨i.isLt, fun _ => hnot⟩)


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

private lemma mem_badPointEndpointBlock_iff_local {a b c r : ℝ}
    (P : Partition a b) {i : ℕ} :
    i ∈ badPointEndpointBlock P c r ↔
      i < P.n ∧ c - r < pointAtNat P i ∧ pointAtNat P (i + 1) < c + r := by
  classical
  simp only [badPointEndpointBlock, Finset.mem_filter, Finset.mem_range] <;> rfl

/-- The endpoint-selected bad cells around `c` are covered by the canonical
consecutive block cut out by the first left and last right partition cutpoints. -/
private lemma badPointEndpointBlock_subset_canonical_Ico_local {a b c r : ℝ}
    (P : Partition a b)
    (hcI : c ∈ Icc a b) (hr : 0 < r) :
    badPointEndpointBlock P c r ⊆
      Finset.Ico (badPointCanonicalLo P c r) (badPointCanonicalHi P c r) := by
  intro i hi_block
  rw [mem_badPointEndpointBlock_iff_local P] at hi_block
  have hi_left : i ∈ badPointLeftCutCandidates P c r := by
    rw [badPointLeftCutCandidates]
    refine Finset.mem_filter.mpr ⟨?_, le_of_lt hi_block.2.1⟩
    exact Finset.mem_range.mpr (Nat.lt_trans hi_block.1 (Nat.lt_succ_self P.n))
  have hi_right : i + 1 ∈ badPointRightCutCandidates P c r := by
    rw [badPointRightCutCandidates]
    refine Finset.mem_filter.mpr ⟨?_, le_of_lt hi_block.2.2⟩
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.succ_le_of_lt hi_block.1))
  rw [Finset.mem_Ico]
  exact ⟨badPointCanonicalLo_le_of_mem_leftCandidates P hcI hr hi_left,
    Nat.lt_of_succ_le
      (le_badPointCanonicalHi_of_mem_rightCandidates P hcI hr hi_right)⟩

private lemma mem_goodRemainder_iff_local {a b x : ℝ} {S : Finset ℝ} {rho : ℝ → ℝ} :
    x ∈ goodRemainder a b S rho ↔
      x ∈ Icc a b ∧ ∀ c : ℝ, c ∈ S → rho c ≤ |x - c| := by
  simp [goodRemainder]

/-- Any two points in one partition cell are separated by at most that cell's
length. -/
private lemma abs_sub_le_cell_length_of_mem_subinterval_local {a b x y : ℝ}
    (P : Partition a b) {i : Fin P.n}
    (hx : x ∈ Partition.subinterval P i)
    (hy : y ∈ Partition.subinterval P i) :
    |x - y| ≤ P.pts i.succ - P.pts i.castSucc := by
  rcases hx with ⟨hix, hxi⟩
  rcases hy with ⟨hiy, hyi⟩
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith

/-- If a partition cell is not contained in the good remainder, then it meets
one of the removed bad-point balls. -/
private lemma exists_bad_point_of_not_subset_goodRemainder_cell_local
    {a b : ℝ} {S : Finset ℝ} {rho : ℝ → ℝ}
    (P : Partition a b) {i : Fin P.n}
    (hcell_not_good :
      ¬ Partition.subinterval P i ⊆ goodRemainder a b S rho) :
    ∃ c : ℝ, c ∈ S ∧ ∃ x : ℝ,
      x ∈ Partition.subinterval P i ∧ |x - c| < rho c := by
  rw [Set.not_subset] at hcell_not_good
  rcases hcell_not_good with ⟨x, hxcell, hxnotgood⟩
  have hxI : x ∈ Icc a b :=
    DarbouxRS.subinterval_subset_Icc_core P hxcell
  rw [mem_goodRemainder_iff_local] at hxnotgood
  have hnot_all : ¬ ∀ c : ℝ, c ∈ S → rho c ≤ |x - c| := by
    intro hall
    exact hxnotgood ⟨hxI, hall⟩
  push Not at hnot_all
  rcases hnot_all with ⟨c, hcS, hclose⟩
  exact ⟨c, hcS, x, hxcell, hclose⟩

/-- A bad cell for the half-radius good remainder meets a half-radius bad ball. -/
private lemma exists_bad_point_half_radius_of_not_subset_goodRemainder_cell_local
    {a b : ℝ} {S : Finset ℝ} {rho : ℝ → ℝ}
    (P : Partition a b) {i : Fin P.n}
    (hcell_not_good :
      ¬ Partition.subinterval P i ⊆
        goodRemainder a b S (fun c : ℝ => rho c / 2)) :
    ∃ c : ℝ, c ∈ S ∧ ∃ x : ℝ,
      x ∈ Partition.subinterval P i ∧ |x - c| < rho c / 2 :=
  exists_bad_point_of_not_subset_goodRemainder_cell_local P hcell_not_good

/-- If a cell meets the half-radius ball around `c` and the mesh is below that
half-radius, then both cell endpoints lie in the full-radius ball around `c`. -/
private lemma partition_cell_endpoints_abs_lt_of_meets_half_radius_local
    {a b c r : ℝ} (P : Partition a b) {i : Fin P.n}
    (_hr : 0 < r)
    (hmesh : P.mesh < r / 2)
    {x : ℝ} (hxcell : x ∈ Partition.subinterval P i)
    (hxclose : |x - c| < r / 2) :
    |P.pts i.castSucc - c| < r ∧ |P.pts i.succ - c| < r := by
  have hleft_mem : P.pts i.castSucc ∈ Partition.subinterval P i :=
    ⟨le_rfl, le_of_lt (P.strict_mono Fin.castSucc_lt_succ)⟩
  have hright_mem : P.pts i.succ ∈ Partition.subinterval P i :=
    ⟨le_of_lt (P.strict_mono Fin.castSucc_lt_succ), le_rfl⟩
  have hleft_len :
      |P.pts i.castSucc - x| ≤ P.pts i.succ - P.pts i.castSucc :=
    abs_sub_le_cell_length_of_mem_subinterval_local P hleft_mem hxcell
  have hright_len :
      |P.pts i.succ - x| ≤ P.pts i.succ - P.pts i.castSucc :=
    abs_sub_le_cell_length_of_mem_subinterval_local P hright_mem hxcell
  have hlen_mesh : P.pts i.succ - P.pts i.castSucc ≤ P.mesh := by
    unfold Partition.mesh
    exact Finset.le_sup'
      (fun j : Fin P.n => P.pts j.succ - P.pts j.castSucc)
      (Finset.mem_univ i)
  have hleft_close : |P.pts i.castSucc - x| < r / 2 :=
    lt_of_le_of_lt (le_trans hleft_len hlen_mesh) hmesh
  have hright_close : |P.pts i.succ - x| < r / 2 :=
    lt_of_le_of_lt (le_trans hright_len hlen_mesh) hmesh
  have hleft_tri :
      |P.pts i.castSucc - c| ≤ |P.pts i.castSucc - x| + |x - c| := by
    have hdecomp : P.pts i.castSucc - c = (P.pts i.castSucc - x) + (x - c) := by ring
    rw [hdecomp]
    exact abs_add_le _ _
  have hright_tri :
      |P.pts i.succ - c| ≤ |P.pts i.succ - x| + |x - c| := by
    have hdecomp : P.pts i.succ - c =
        (P.pts i.succ - x) + (x - c) := by ring
    rw [hdecomp]
    exact abs_add_le _ _
  constructor <;> linarith

/-- With mesh below every half-radius, each half-radius bad cell is covered by
the endpoint block of some bad point. -/
private lemma badCellIndices_half_radius_subset_badPointEndpointBlocks_local {a b : ℝ}
    (P : Partition a b) (S : Finset ℝ) (rho : ℝ → ℝ)
    (hrho_pos : ∀ c : ℝ, c ∈ S → 0 < rho c)
    (hmesh : ∀ c : ℝ, c ∈ S → P.mesh < rho c / 2) :
    badCellIndices P S (fun c : ℝ => rho c / 2) ⊆
      S.biUnion (fun c : ℝ => badPointEndpointBlock P c (rho c)) := by
  classical
  intro i hi_bad
  rcases (mem_badCellIndices_iff_local P S (fun c : ℝ => rho c / 2)).1 hi_bad with
    ⟨hi, hnot_good⟩
  rcases exists_bad_point_half_radius_of_not_subset_goodRemainder_cell_local
      P (hnot_good hi) with
    ⟨c, hcS, x, hxcell, hxclose⟩
  rcases partition_cell_endpoints_abs_lt_of_meets_half_radius_local
      P (hrho_pos c hcS) (hmesh c hcS) hxcell hxclose with
    ⟨hleft_abs, hright_abs⟩
  refine Finset.mem_biUnion.mpr ⟨c, hcS, ?_⟩
  rw [mem_badPointEndpointBlock_iff_local P]
  refine ⟨hi, ?_, ?_⟩
  · have hleft_abs' : |pointAtNat P i - c| < rho c := by
      rw [pointAtNat_eq P (Nat.le_of_lt hi)]
      simpa using hleft_abs
    have hleft := (abs_lt.mp hleft_abs').1
    linarith
  · have hright_abs' : |pointAtNat P (i + 1) - c| < rho c := by
      rw [pointAtNat_eq P (Nat.succ_le_of_lt hi)]
      simpa using hright_abs
    have hright := (abs_lt.mp hright_abs').2
    linarith

/-- Pairwise-disjoint bad-point intervals induce pairwise-disjoint canonical
consecutive partition-index blocks. -/
private lemma badPointCanonicalIcoBlocks_pairwiseDisjoint_of_pairwiseDisjoint_Ioo_local
    {a b : ℝ} (P : Partition a b)
    (S : Finset ℝ) (rho : ℝ → ℝ)
    (hcI : ∀ c : ℝ, c ∈ S → c ∈ Icc a b)
    (hrho_pos : ∀ c : ℝ, c ∈ S → 0 < rho c)
    (hsep :
      (↑S : Set ℝ).PairwiseDisjoint
        (fun c : ℝ => Set.Ioo (c - rho c) (c + rho c))) :
    (↑S : Set ℝ).PairwiseDisjoint
      (fun c : ℝ =>
        Finset.Ico (badPointCanonicalLo P c (rho c))
          (badPointCanonicalHi P c (rho c))) := by
  classical
  rw [Set.PairwiseDisjoint] at hsep ⊢
  intro c hc d hd hne
  change Disjoint
    (Finset.Ico (badPointCanonicalLo P c (rho c))
      (badPointCanonicalHi P c (rho c)))
    (Finset.Ico (badPointCanonicalLo P d (rho d))
      (badPointCanonicalHi P d (rho d)))
  rw [Finset.disjoint_left]
  intro i hiC hiD
  rw [Finset.mem_Ico] at hiC hiD
  have hhiC_le_n := badPointCanonicalHi_le_n P (hcI c hc) (hrho_pos c hc)
  have hhiD_le_n := badPointCanonicalHi_le_n P (hcI d hd) (hrho_pos d hd)
  have hi_lt_n : i < P.n := lt_of_lt_of_le hiC.2 hhiC_le_n
  have hstep : pointAtNat P i < pointAtNat P (i + 1) :=
    pointAtNat_strictMono P (Nat.le_of_lt hi_lt_n) (Nat.succ_le_of_lt hi_lt_n) (by omega)
  let y : ℝ := (pointAtNat P i + pointAtNat P (i + 1)) / 2
  have hleftC : c - rho c ≤ pointAtNat P i := by
    exact le_trans
      (badPointCanonicalLo_left_bound P (hcI c hc) (hrho_pos c hc))
      (pointAtNat_mono P
        (badPointCanonicalLo_le_n P (hcI c hc) (hrho_pos c hc))
        (Nat.le_of_lt hi_lt_n) hiC.1)
  have hrightC : pointAtNat P (i + 1) ≤ c + rho c := by
    exact le_trans
      (pointAtNat_mono P (Nat.succ_le_of_lt hi_lt_n) hhiC_le_n
        (Nat.succ_le_of_lt hiC.2))
      (badPointCanonicalHi_right_bound P (hcI c hc) (hrho_pos c hc))
  have hleftD : d - rho d ≤ pointAtNat P i := by
    exact le_trans
      (badPointCanonicalLo_left_bound P (hcI d hd) (hrho_pos d hd))
      (pointAtNat_mono P
        (badPointCanonicalLo_le_n P (hcI d hd) (hrho_pos d hd))
        (Nat.le_of_lt hi_lt_n) hiD.1)
  have hrightD : pointAtNat P (i + 1) ≤ d + rho d := by
    exact le_trans
      (pointAtNat_mono P (Nat.succ_le_of_lt hi_lt_n) hhiD_le_n
        (Nat.succ_le_of_lt hiD.2))
      (badPointCanonicalHi_right_bound P (hcI d hd) (hrho_pos d hd))
  have hy_left : pointAtNat P i < y := by
    dsimp [y]
    linarith
  have hy_right : y < pointAtNat P (i + 1) := by
    dsimp [y]
    linarith
  have hyC : y ∈ Set.Ioo (c - rho c) (c + rho c) :=
    ⟨lt_of_le_of_lt hleftC hy_left, lt_of_lt_of_le hy_right hrightC⟩
  have hyD : y ∈ Set.Ioo (d - rho d) (d + rho d) :=
    ⟨lt_of_le_of_lt hleftD hy_left, lt_of_lt_of_le hy_right hrightD⟩
  have hempty :
      Set.Ioo (c - rho c) (c + rho c) ∩
          Set.Ioo (d - rho d) (d + rho d) = (∅ : Set ℝ) :=
    Set.disjoint_iff_inter_eq_empty.mp (hsep hc hd hne)
  have hyempty : y ∈ (∅ : Set ℝ) := by
    simpa [hempty] using
      (show y ∈
          Set.Ioo (c - rho c) (c + rho c) ∩
            Set.Ioo (d - rho d) (d + rho d) from
        ⟨hyC, hyD⟩)
  exact hyempty

/-- If all values of `f` on a partition cell differ by at most `eta`, then
the cell upper-minus-lower step is at most `eta`. -/
private lemma upperStep_sub_lowerStep_le_of_subinterval_oscillation_bound_local
    {f : ℝ → ℝ} {a b eta : ℝ}
    (P : Partition a b) (i : Fin P.n)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (hosc :
      ∀ x, x ∈ Partition.subinterval P i →
      ∀ y, y ∈ Partition.subinterval P i → |f x - f y| ≤ eta) :
    upperStep P f i - lowerStep P f i ≤ eta := by
  let cell := Partition.subinterval P i
  have hcell_nonempty : (f '' cell).Nonempty := by
    refine ⟨f (P.pts i.castSucc), ?_⟩
    refine ⟨P.pts i.castSucc, ?_, rfl⟩
    exact ⟨le_rfl, le_of_lt (P.strict_mono Fin.castSucc_lt_succ)⟩
  have hcellAbove : BddAbove (f '' cell) :=
    BddAbove.mono (Set.image_mono (DarbouxRS.subinterval_subset_Icc_core P)) hAbove
  have hcellBelow : BddBelow (f '' cell) :=
    BddBelow.mono (Set.image_mono (DarbouxRS.subinterval_subset_Icc_core P)) hBelow
  have hsup_le :
      sSup (f '' cell) ≤ sInf (f '' cell) + eta := by
    refine csSup_le hcell_nonempty ?_
    rintro _ ⟨x, hx, rfl⟩
    have hle_inf : f x - eta ≤ sInf (f '' cell) := by
      refine le_csInf hcell_nonempty ?_
      rintro _ ⟨y, hy, rfl⟩
      have hxy : f x - f y ≤ eta := (abs_le.mp (hosc x hx y hy)).2
      linarith
    linarith
  unfold upperStep lowerStep
  linarith

/-- A uniform absolute-value bound on `[a,b]` gives a coarse cell oscillation
bound. This is the estimate used for cells near discontinuities. -/
private lemma upperStep_sub_lowerStep_le_two_mul_abs_bound_local
    {f : ℝ → ℝ} {a b C : ℝ}
    (P : Partition a b) (i : Fin P.n)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (hC : ∀ x : ℝ, x ∈ Icc a b → |f x| ≤ C) :
    upperStep P f i - lowerStep P f i ≤ 2 * C := by
  refine upperStep_sub_lowerStep_le_of_subinterval_oscillation_bound_local
    P i hAbove hBelow ?_
  intro x hx y hy
  have hxI : x ∈ Icc a b := DarbouxRS.subinterval_subset_Icc_core P hx
  have hyI : y ∈ Icc a b := DarbouxRS.subinterval_subset_Icc_core P hy
  have hxC := hC x hxI
  have hyC := hC y hyI
  have htri : |f x - f y| ≤ |f x| + |f y| := by
    calc
      |f x - f y| = |f x + -f y| := by ring_nf
      _ ≤ |f x| + |-f y| := abs_add_le (f x) (-f y)
      _ = |f x| + |f y| := by rw [abs_neg]
  linarith

private lemma sum_adjacent_sub_local {n : ℕ} (g : Fin (n + 1) → ℝ) :
    (∑ i : Fin n, (g i.succ - g i.castSucc)) =
      g (Fin.last n) - g 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_succ]
      have htail := ih (fun i : Fin (n + 1) => g i.succ)
      have htail' :
          (∑ i : Fin n, (g i.succ.succ - g i.succ.castSucc)) =
            g (Fin.last n).succ - g (Fin.succ 0) := by
        simpa only [Fin.succ_castSucc] using htail
      rw [htail']
      simp

/-- Split the partition oscillation into a small good-cell contribution plus
a coarse bad-cell contribution supported on a chosen finite index set. -/
private lemma partitionOscillation_le_good_bad_split_local
    {f α : ℝ → ℝ} {a b C eta : ℝ}
    (hs : SourceHypotheses a b f α)
    (P : Partition a b)
    (B : Finset ℕ)
    (heta_nonneg : 0 ≤ eta)
    (hgood :
      ∀ i : Fin P.n, i.val ∉ B →
        upperStep P f i - lowerStep P f i ≤ eta)
    (hbad :
      ∀ i : Fin P.n, i.val ∈ B →
        upperStep P f i - lowerStep P f i ≤ 2 * C) :
    partitionOscillation P f α ≤
      eta * (α b - α a) +
        2 * C *
          (∑ i ∈ (Finset.univ : Finset (Fin P.n)).filter (fun i => i.val ∈ B),
            (α (P.pts i.succ) - α (P.pts i.castSucc))) := by
  rcases hs with ⟨hab, hAbove, hBelow, hmono⟩
  unfold partitionOscillation
  let inc : Fin P.n → ℝ := fun i => α (P.pts i.succ) - α (P.pts i.castSucc)
  have htel :
      (∑ i : Fin P.n, inc i) = α b - α a := by
    simpa [inc, P.pts_start, P.pts_end] using sum_adjacent_sub_local (fun i => α (P.pts i))
  have hsum_le :
      (∑ i : Fin P.n,
        (upperStep P f i - lowerStep P f i) * inc i)
        ≤ ∑ i : Fin P.n,
            (eta * inc i + if i.val ∈ B then (2 * C) * inc i else 0) := by
    refine Finset.sum_le_sum ?_
    intro i hi_mem
    have hinc_nonneg : 0 ≤ inc i :=
      DarbouxRS.partition_increment_nonneg_of_source_core_local P
        ⟨hab, hAbove, hBelow, hmono⟩
    by_cases hiB : i.val ∈ B
    · have hterm :
          (upperStep P f i - lowerStep P f i) * inc i ≤
            (2 * C) * inc i :=
        mul_le_mul_of_nonneg_right (hbad i hiB) hinc_nonneg
      have heta_inc : 0 ≤ eta * inc i := mul_nonneg heta_nonneg hinc_nonneg
      simp [hiB]
      linarith
    · have hterm :
          (upperStep P f i - lowerStep P f i) * inc i ≤
            eta * inc i :=
        mul_le_mul_of_nonneg_right (hgood i hiB) hinc_nonneg
      simp [hiB]
      exact hterm
  have hsum_eq :
      (∑ i : Fin P.n,
            (eta * inc i + if i.val ∈ B then (2 * C) * inc i else 0)) =
        eta * (α b - α a) +
          2 * C *
            (∑ i ∈ (Finset.univ : Finset (Fin P.n)).filter (fun i => i.val ∈ B), inc i) := by
    rw [Finset.sum_add_distrib]
    have hfirst :
        (∑ i : Fin P.n, eta * inc i) = eta * (α b - α a) := by
      rw [← Finset.mul_sum, htel]
    have hsecond :
        (∑ i : Fin P.n, (if i.val ∈ B then (2 * C) * inc i else 0)) =
          2 * C *
            (∑ i ∈ (Finset.univ : Finset (Fin P.n)).filter (fun i => i.val ∈ B), inc i) := by
      calc
        (∑ i : Fin P.n, (if i.val ∈ B then (2 * C) * inc i else 0))
            = ∑ i ∈ (Finset.univ : Finset (Fin P.n)).filter (fun i => i.val ∈ B),
                (2 * C) * inc i := by
              rw [Finset.sum_filter]
        _ = 2 * C *
              (∑ i ∈ (Finset.univ : Finset (Fin P.n)).filter (fun i => i.val ∈ B), inc i) := by
              rw [Finset.mul_sum]
    rw [hfirst, hsecond]
  exact le_trans hsum_le (le_of_eq hsum_eq)

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

lemma badCellIndices_half_radius_subset_Ico_blocks_of_endpointBlock_cover
    {a b : ℝ}
    (P : Partition a b) (S : Finset ℝ) (rho : ℝ → ℝ)
    (lo hi : ℝ → ℕ)
    (hrho_pos : ∀ c : ℝ, c ∈ S → 0 < rho c)
    (hmesh : ∀ c : ℝ, c ∈ S → P.mesh < rho c / 2)
    (hblock_cover :
      ∀ c : ℝ, c ∈ S →
        badPointEndpointBlock P c (rho c) ⊆ Finset.Ico (lo c) (hi c)) :
    badCellIndices P S (fun c : ℝ => rho c / 2) ⊆
      S.biUnion (fun c : ℝ => Finset.Ico (lo c) (hi c)) := by
  classical
  intro i hi_bad
  have hendpoint_cover :=
    badCellIndices_half_radius_subset_badPointEndpointBlocks_local
      P S rho hrho_pos hmesh hi_bad
  rcases (Finset.mem_biUnion.mp hendpoint_cover) with ⟨c, hcS, hi_block⟩
  exact Finset.mem_biUnion.mpr ⟨c, hcS, hblock_cover c hcS hi_block⟩

private lemma partition_increment_sum_badCellIndices_half_radius_le_bad_intervals
    {α : ℝ → ℝ} {a b : ℝ}
    (hα_mono : Monotone α)
    (P : Partition a b)
    (S : Finset ℝ) (rho : ℝ → ℝ) (lo hi : ℝ → ℕ)
    (hrho_pos : ∀ c : ℝ, c ∈ S → 0 < rho c)
    (hmesh : ∀ c : ℝ, c ∈ S → P.mesh < rho c / 2)
    (hblock_cover :
      ∀ c : ℝ, c ∈ S →
        badPointEndpointBlock P c (rho c) ⊆ Finset.Ico (lo c) (hi c))
    (hdisj :
      (↑S : Set ℝ).PairwiseDisjoint
        (fun c : ℝ => Finset.Ico (lo c) (hi c)))
    (hlohi : ∀ c : ℝ, c ∈ S → lo c ≤ hi c)
    (hhi : ∀ c : ℝ, c ∈ S → hi c ≤ P.n)
    (hleft : ∀ c : ℝ, c ∈ S → c - rho c ≤ pointAtNat P (lo c))
    (hright : ∀ c : ℝ, c ∈ S → pointAtNat P (hi c) ≤ c + rho c) :
    (∑ i ∈ badCellIndices P S (fun c : ℝ => rho c / 2),
        (α (pointAtNat P (i + 1)) - α (pointAtNat P i))) ≤
      ∑ c ∈ S, (α (c + rho c) - α (c - rho c)) := by
  classical
  refine partition_increment_sum_le_bad_intervals_of_disjoint_Ico_cover
    hα_mono P (badCellIndices P S (fun c : ℝ => rho c / 2))
    S rho lo hi hdisj ?_ hlohi hhi hleft hright
  exact badCellIndices_half_radius_subset_Ico_blocks_of_endpointBlock_cover
    P S rho lo hi hrho_pos hmesh hblock_cover

private lemma partition_increment_sum_badCellIndices_half_radius_le_bad_intervals_canonical
    {α : ℝ → ℝ} {a b : ℝ}
    (hα_mono : Monotone α)
    (P : Partition a b)
    (S : Finset ℝ) (rho : ℝ → ℝ)
    (hcI : ∀ c : ℝ, c ∈ S → c ∈ Icc a b)
    (hrho_pos : ∀ c : ℝ, c ∈ S → 0 < rho c)
    (hmesh : ∀ c : ℝ, c ∈ S → P.mesh < rho c / 2)
    (hsep :
      (↑S : Set ℝ).PairwiseDisjoint
        (fun c : ℝ => Set.Ioo (c - rho c) (c + rho c))) :
    (∑ i ∈ badCellIndices P S (fun c : ℝ => rho c / 2),
        (α (pointAtNat P (i + 1)) - α (pointAtNat P i))) ≤
      ∑ c ∈ S, (α (c + rho c) - α (c - rho c)) := by
  refine partition_increment_sum_badCellIndices_half_radius_le_bad_intervals
    hα_mono P S rho
    (fun c : ℝ => badPointCanonicalLo P c (rho c))
    (fun c : ℝ => badPointCanonicalHi P c (rho c))
    hrho_pos hmesh ?_ ?_ ?_ ?_ ?_ ?_
  · intro c hc
    exact badPointEndpointBlock_subset_canonical_Ico_local P (hcI c hc) (hrho_pos c hc)
  · exact badPointCanonicalIcoBlocks_pairwiseDisjoint_of_pairwiseDisjoint_Ioo_local
      P S rho hcI hrho_pos hsep
  · intro c hc
    exact badPointCanonicalLo_le_hi_of_mesh P (hcI c hc) (hrho_pos c hc) (hmesh c hc)
  · intro c hc
    exact badPointCanonicalHi_le_n P (hcI c hc) (hrho_pos c hc)
  · intro c hc
    exact badPointCanonicalLo_left_bound P (hcI c hc) (hrho_pos c hc)
  · intro c hc
    exact badPointCanonicalHi_right_bound P (hcI c hc) (hrho_pos c hc)

private lemma partitionOscillation_le_goodRemainder_badCell_split
    {f α : ℝ → ℝ} {a b C eta δgood : ℝ}
    {S : Finset ℝ} {rho : ℝ → ℝ}
    (hs : SourceHypotheses a b f α)
    (P : Partition a b)
    (hC : ∀ x : ℝ, x ∈ Icc a b → |f x| ≤ C)
    (heta_nonneg : 0 ≤ eta)
    (hgood_step :
      ∀ (P' : Partition a b) (i : Fin P'.n),
        P'.mesh < δgood →
        Partition.subinterval P' i ⊆ goodRemainder a b S rho →
          upperStep P' f i - lowerStep P' f i < eta)
    (hmesh_good : P.mesh < δgood) :
    partitionOscillation P f α ≤
      eta * (α b - α a) +
        2 * C *
          (∑ i ∈ badCellIndices P S rho,
            (α (pointAtNat P (i + 1)) - α (pointAtNat P i))) := by
  rcases hs with ⟨hab, hAbove, hBelow, hmono⟩
  let hs' : SourceHypotheses a b f α :=
    ⟨hab, hAbove, hBelow, hmono⟩
  have hsplit := partitionOscillation_le_good_bad_split_local
    (f := f) (α := α) (a := a) (b := b) (C := C) (eta := eta)
    hs' P (badCellIndices P S rho) heta_nonneg
    (fun i hi_not_bad =>
      le_of_lt (hgood_step P i hmesh_good
        (cell_subset_goodRemainder_of_not_mem_badCellIndices_local P S rho i hi_not_bad)))
    (fun i _hi_bad =>
      upperStep_sub_lowerStep_le_two_mul_abs_bound_local P i hAbove hBelow hC)
  have hfin_to_range :
      (∑ i ∈ (Finset.univ : Finset (Fin P.n)).filter
          (fun i => i.val ∈ badCellIndices P S rho),
          (α (P.pts i.succ) - α (P.pts i.castSucc))) =
        ∑ i ∈ (Finset.range P.n).filter (fun i => i ∈ badCellIndices P S rho),
          (α (pointAtNat P (i + 1)) - α (pointAtNat P i)) := by
    rw [Finset.sum_filter]
    calc
      (∑ i : Fin P.n,
          if i.val ∈ badCellIndices P S rho then
            α (P.pts i.succ) - α (P.pts i.castSucc)
          else 0) =
          ∑ i : Fin P.n,
            if i.val ∈ badCellIndices P S rho then
              α (pointAtNat P (i.val + 1)) - α (pointAtNat P i.val)
            else 0 := by
              refine Finset.sum_congr rfl ?_
              intro i _
              by_cases hi : i.val ∈ badCellIndices P S rho
              · simp only [hi, if_true]
                rw [pointAtNat_eq P (Nat.succ_le_of_lt i.isLt),
                  pointAtNat_eq P (Nat.le_of_lt i.isLt)]
                rfl
              · simp [hi]
      _ = ∑ i ∈ Finset.range P.n,
            if i ∈ badCellIndices P S rho then
              α (pointAtNat P (i + 1)) - α (pointAtNat P i)
            else 0 := by
              exact Fin.sum_univ_eq_sum_range (fun i : ℕ =>
                if i ∈ badCellIndices P S rho then
                  α (pointAtNat P (i + 1)) - α (pointAtNat P i)
                else 0) P.n
      _ = ∑ i ∈ (Finset.range P.n).filter (fun i => i ∈ badCellIndices P S rho),
            (α (pointAtNat P (i + 1)) - α (pointAtNat P i)) := by
              rw [Finset.sum_filter]
  have hfilter_eq :
      (Finset.range P.n).filter (fun i => i ∈ badCellIndices P S rho) =
        badCellIndices P S rho := by
    ext i
    constructor
    · intro hi
      exact (Finset.mem_filter.mp hi).2
    · intro hi
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr ((mem_badCellIndices_iff_local P S rho).mp hi).1, hi⟩
  rw [hfin_to_range, hfilter_eq] at hsplit
  exact hsplit
end Thm11SourceRoute


