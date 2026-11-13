-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_4_F001
-- name    : ProbabilityTheory_chapter_01_thm_1_4_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:54:52.033431+00:00
-- url     : https://prove2.me/theorems/fbb72cd4-9a02-420f-935e-2e255cbd6628
-- title:
--   Chapter 1, thm_1_4: supporting Lean bundle F001
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_4`: `partitionOscillation`, `upperSum_sub_lowerSum_eq_partitionOscillation`, `exists_pos_abs_bound_on_Icc_of_bddAbove_bddBelow`, `upperStep_sub_lowerStep_le_of_subinterval_oscillation_bound`, `abs_sub_le_cell_length_of_mem_subinterval`, and 7 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_4.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F000
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

open Set MeasureTheory
open scoped BigOperators Pointwise Interval

noncomputable section

namespace Thm_1_4

noncomputable def partitionOscillation {a b : ℝ}
    (P : Partition a b) (f α : ℝ → ℝ) : ℝ :=
  ∑ i : Fin P.n,
    (upperStep P f i - lowerStep P f i) *
      (α (P.pts i.succ) - α (P.pts i.castSucc))
lemma upperSum_sub_lowerSum_eq_partitionOscillation {f α : ℝ → ℝ} {a b : ℝ}
    (P : Partition a b) :
    upperSum P f α - lowerSum P f α =
      partitionOscillation P f α := by
  unfold partitionOscillation upperSum lowerSum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring
lemma exists_pos_abs_bound_on_Icc_of_bddAbove_bddBelow {f : ℝ → ℝ} {a b : ℝ}
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, x ∈ Icc a b → |f x| ≤ C := by
  rcases hAbove with ⟨U, hU⟩
  rcases hBelow with ⟨L, hL⟩
  refine ⟨max |U| |L| + 1, ?_, ?_⟩
  · positivity
  · intro x hx
    have hxU : f x ≤ U := hU ⟨x, hx, rfl⟩
    have hxL : L ≤ f x := hL ⟨x, hx, rfl⟩
    refine abs_le.mpr ⟨?_, ?_⟩
    · have hL_abs : -|L| ≤ L := neg_abs_le L
      have hC_abs : |L| ≤ max |U| |L| + 1 := by
        calc
          |L| ≤ max |U| |L| := le_max_right _ _
          _ ≤ max |U| |L| + 1 := by linarith
      linarith
    · have hU_abs : U ≤ |U| := le_abs_self U
      have hC_abs : |U| ≤ max |U| |L| + 1 := by
        calc
          |U| ≤ max |U| |L| := le_max_left _ _
          _ ≤ max |U| |L| + 1 := by linarith
      linarith
lemma upperStep_sub_lowerStep_le_of_subinterval_oscillation_bound
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
    BddAbove.mono
      (Set.image_mono (DarbouxRS.subinterval_subset_Icc_core P (i := i)))
      hAbove
  have hcellBelow : BddBelow (f '' cell) :=
    BddBelow.mono
      (Set.image_mono (DarbouxRS.subinterval_subset_Icc_core P (i := i)))
      hBelow
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
lemma abs_sub_le_cell_length_of_mem_subinterval {a b x y : ℝ}
    (P : Partition a b) {i : Fin P.n}
    (hx : x ∈ Partition.subinterval P i)
    (hy : y ∈ Partition.subinterval P i) :
    |x - y| ≤ P.pts i.succ - P.pts i.castSucc := by
  rcases hx with ⟨hix, hxi⟩
  rcases hy with ⟨hiy, hyi⟩
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
lemma partition_length_le_mesh_core {a b : ℝ}
    (P : Partition a b) (i : Fin P.n) :
    P.pts i.succ - P.pts i.castSucc ≤ P.mesh := by
  unfold Partition.mesh
  exact Finset.le_sup'
    (fun j : Fin P.n => P.pts j.succ - P.pts j.castSucc)
    (by simp : i ∈ (Finset.univ : Finset (Fin P.n)))

def ClosedIntervalDarbouxGapSmall
    (a b : ℝ) (f α : ℝ → ℝ) : Prop :=
  ∀ eps > 0, ∃ δ > 0, ∀ P : Partition a b,
    P.mesh < δ →
      upperSum P f α - lowerSum P f α < eps

private noncomputable def ptNat {a b : ℝ} (P : Partition a b) (k : ℕ) : ℝ :=
  if hk : k ≤ P.n then
    P.pts ⟨k, Nat.lt_succ_of_le hk⟩
  else
    P.pts (Fin.last P.n)
private lemma ptNat_zero {a b : ℝ} (P : Partition a b) :
    ptNat P 0 = a := by
  unfold ptNat
  rw [dif_pos (Nat.zero_le P.n)]
  simpa using P.pts_start
private lemma ptNat_last {a b : ℝ} (P : Partition a b) :
    ptNat P P.n = b := by
  unfold ptNat
  rw [dif_pos le_rfl]
  have hfin :
      (⟨P.n, Nat.lt_succ_self P.n⟩ : Fin (P.n + 1)) = Fin.last P.n := by
    ext
    simp
  simpa [hfin] using P.pts_end
private lemma ptNat_of_lt {a b : ℝ} (P : Partition a b) {k : ℕ}
    (hk : k < P.n) :
    ptNat P k = P.pts (Fin.castSucc (⟨k, hk⟩ : Fin P.n)) := by
  unfold ptNat
  rw [dif_pos (le_of_lt hk)]
  congr
private lemma ptNat_succ_of_lt {a b : ℝ} (P : Partition a b) {k : ℕ}
    (hk : k < P.n) :
    ptNat P (k + 1) = P.pts (Fin.succ (⟨k, hk⟩ : Fin P.n)) := by
  unfold ptNat
  rw [dif_pos (Nat.succ_le_of_lt hk)]
  congr

end Thm_1_4


