-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F005
-- name    : ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F005
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T23:13:34.573005+00:00
-- url     : https://prove2.me/theorems/62e5478c-fa05-4bd6-8c20-da3eaa2fb013
-- title:
--   Chapter 1, thm_1_1_bad_cells: supporting Lean bundle F005
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_1_bad_cells`: `partition_cell_increment_le_bad_interval`, `partition_cell_increment_le_bad_interval_of_half_radius_hit`, `pointAtNat`, `pointAtNat_eq`, `pointAtNat_zero`, and 5 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_bad_cells.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F000
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

noncomputable def badPointEndpointBlock {a b : ℝ}
    (P : Partition a b) (c r : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range P.n).filter
    (fun i => c - r < pointAtNat P i ∧ pointAtNat P (i + 1) < c + r)
private lemma mem_badPointEndpointBlock_iff {a b c r : ℝ}
    (P : Partition a b) {i : ℕ} :
    i ∈ badPointEndpointBlock P c r ↔
      i < P.n ∧ c - r < pointAtNat P i ∧ pointAtNat P (i + 1) < c + r := by
  classical
  simp [badPointEndpointBlock]
end Thm11SourceRoute


