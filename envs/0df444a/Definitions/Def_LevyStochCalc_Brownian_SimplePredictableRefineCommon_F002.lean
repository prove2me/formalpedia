-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineCommon_F002
-- name    : LevyStochCalc_Brownian_SimplePredictableRefineCommon_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T15:07:42.180424+00:00
-- url     : https://prove2.me/theorems/06a5162d-5d9b-4756-a46e-64edc0e37234
-- title:
--   Source declarations: LevyStochCalc.Brownian.SimplePredictableRefineCommon
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.SimplePredictableRefineCommon. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineCommon_F000
import Definitions.Def_SourceProof_04cf3c59e383c3e0f39e729b
import Definitions.Def_SourceProof_3281419cf2ade5797eb4da52
import Definitions.Def_SourceProof_a9fc753424ae9a1369612fa3

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Common refinement of two simple predictables and the difference isometry

The common refinement of two `SimplePredictable Ω T` sharing an endpoint: the
merged set of partition points, the merged partition `SimplePredictable.mergedπ`
with its two refining index maps, the induced refinements
`SimplePredictable.commonRefinement_left`/`_right` and their difference
`SimplePredictable.sub_on_common`. These give the difference isometry for simple
integrals (`SimplePredictable.diff_isometry_simple`) and the Cauchy property of
the simple integrals of an `L²`-Cauchy sequence of simple predictables
(`cauchy_of_L2_dense_simple`).
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- **C0b.4-pre13: every `H₁.partition i` is in the range of `mergedπ`.**
The range of `orderEmbOfFin` is the underlying Finset (via
`Finset.range_orderEmbOfFin`). -/
lemma SimplePredictable.mergedπ_refines_left
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T) (i : Fin (H₁.N + 1)) :
    ∃ k : Fin (H₁.mergedM H₂ + 1), H₁.mergedπ H₂ k = H₁.partition i := by
  unfold SimplePredictable.mergedπ
  have h_in_range : H₁.partition i ∈ Set.range
      ⇑((H₁.mergedPartitionPoints H₂).orderEmbOfFin (H₁.mergedM_card_eq H₂)) := by
    rw [Finset.range_orderEmbOfFin]
    exact_mod_cast H₁.partition_mem_mergedPartitionPoints_left H₂ i
  exact h_in_range
/-- **C0b.4-pre14: every `H₂.partition i` is in the range of `mergedπ`.** -/
lemma SimplePredictable.mergedπ_refines_right
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T) (i : Fin (H₂.N + 1)) :
    ∃ k : Fin (H₁.mergedM H₂ + 1), H₁.mergedπ H₂ k = H₂.partition i := by
  unfold SimplePredictable.mergedπ
  have h_in_range : H₂.partition i ∈ Set.range
      ⇑((H₁.mergedPartitionPoints H₂).orderEmbOfFin (H₁.mergedM_card_eq H₂)) := by
    rw [Finset.range_orderEmbOfFin]
    exact_mod_cast H₁.partition_mem_mergedPartitionPoints_right H₂ i
  exact h_in_range
/-- **C0b.4-pre15: existence of left index map.** For each merged tile `j`,
there is an `H₁` tile `i` whose interval contains the merged tile.

Proof: apply `strictMono_partition_tiles` to `H₁.partition` with
`s = mergedπ j.succ` to get `i` with `H₁.partition i.castSucc < s` and
`s ≤ H₁.partition i.succ`. This gives the right inclusion.
For the left inclusion, suppose for contradiction
`mergedπ j.castSucc < H₁.partition i.castSucc`. Since `H₁.partition i.castSucc`
is in the merged set, it equals `mergedπ k` for some `k`. Then
`mergedπ j.castSucc < mergedπ k < mergedπ j.succ`, so `j.castSucc < k < j.succ`,
contradicting `j.succ.val = j.castSucc.val + 1`. -/
private lemma SimplePredictable.exists_mergedIdxMap_left
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (j : Fin (H₁.mergedM H₂)) :
    ∃ i : Fin H₁.N,
      H₁.partition i.castSucc ≤ H₁.mergedπ H₂ j.castSucc ∧
      H₁.mergedπ H₂ j.succ ≤ H₁.partition i.succ := by
  -- Bounds on s = mergedπ j.succ to apply strictMono_partition_tiles
  have h_pos : H₁.partition 0 < H₁.mergedπ H₂ j.succ := by
    rw [H₁.partition_zero, ← (_root_.Prove2MeSourceProof.h_3281419cf2ade5797eb4da52 H₁) H₂]
    exact (H₁.mergedπ_strictMono H₂) (Fin.succ_pos j)
  have h_le_endpt : H₁.mergedπ H₂ j.succ ≤ H₁.partition (Fin.last H₁.N) := by
    rw [← (_root_.Prove2MeSourceProof.h_04cf3c59e383c3e0f39e729b H₁) H₂ h_eq]
    exact (H₁.mergedπ_strictMono H₂).monotone (Fin.le_last j.succ)
  obtain ⟨i, h_lt, h_le⟩ :=
    _root_.Prove2MeSourceProof.h_a9fc753424ae9a1369612fa3 H₁.partition_strictMono h_pos h_le_endpt
  refine ⟨i, ?_, h_le⟩
  by_contra h_not
  push Not at h_not
  -- h_not : H₁.mergedπ H₂ j.castSucc < H₁.partition i.castSucc
  obtain ⟨k, hk⟩ := H₁.mergedπ_refines_left H₂ i.castSucc
  rw [← hk] at h_not h_lt
  have h_jcs_lt_k : j.castSucc < k :=
    (H₁.mergedπ_strictMono H₂).lt_iff_lt.mp h_not
  have h_k_lt_jsc : k < j.succ :=
    (H₁.mergedπ_strictMono H₂).lt_iff_lt.mp h_lt
  have hj_cs_val : j.castSucc.val = j.val := Fin.val_castSucc j
  have hj_succ_val : j.succ.val = j.val + 1 := Fin.val_succ j
  have h1 : j.castSucc.val < k.val := h_jcs_lt_k
  have h2 : k.val < j.succ.val := h_k_lt_jsc
  omega
/-- **C0b.4-pre16: existence of right index map.** Mirror of
`exists_mergedIdxMap_left` for the second SimplePredictable. -/
private lemma SimplePredictable.exists_mergedIdxMap_right
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (j : Fin (H₁.mergedM H₂)) :
    ∃ i : Fin H₂.N,
      H₂.partition i.castSucc ≤ H₁.mergedπ H₂ j.castSucc ∧
      H₁.mergedπ H₂ j.succ ≤ H₂.partition i.succ := by
  have h_pos : H₂.partition 0 < H₁.mergedπ H₂ j.succ := by
    rw [H₂.partition_zero, ← (_root_.Prove2MeSourceProof.h_3281419cf2ade5797eb4da52 H₁) H₂]
    exact (H₁.mergedπ_strictMono H₂) (Fin.succ_pos j)
  have h_le_endpt : H₁.mergedπ H₂ j.succ ≤ H₂.partition (Fin.last H₂.N) := by
    rw [← h_eq, ← (_root_.Prove2MeSourceProof.h_04cf3c59e383c3e0f39e729b H₁) H₂ h_eq]
    exact (H₁.mergedπ_strictMono H₂).monotone (Fin.le_last j.succ)
  obtain ⟨i, h_lt, h_le⟩ :=
    _root_.Prove2MeSourceProof.h_a9fc753424ae9a1369612fa3 H₂.partition_strictMono h_pos h_le_endpt
  refine ⟨i, ?_, h_le⟩
  by_contra h_not
  push Not at h_not
  obtain ⟨k, hk⟩ := H₁.mergedπ_refines_right H₂ i.castSucc
  rw [← hk] at h_not h_lt
  have h_jcs_lt_k : j.castSucc < k :=
    (H₁.mergedπ_strictMono H₂).lt_iff_lt.mp h_not
  have h_k_lt_jsc : k < j.succ :=
    (H₁.mergedπ_strictMono H₂).lt_iff_lt.mp h_lt
  have hj_cs_val : j.castSucc.val = j.val := Fin.val_castSucc j
  have hj_succ_val : j.succ.val = j.val + 1 := Fin.val_succ j
  have h1 : j.castSucc.val < k.val := h_jcs_lt_k
  have h2 : k.val < j.succ.val := h_k_lt_jsc
  omega
/-- **C0b.4-pre17: left index map.** For each merged tile `j`, the
unique `H₁` tile whose interval contains it. Extracted via Choice
from `exists_mergedIdxMap_left`. -/
noncomputable def SimplePredictable.mergedIdxMap_left
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (j : Fin (H₁.mergedM H₂)) : Fin H₁.N :=
  (H₁.exists_mergedIdxMap_left H₂ h_eq j).choose
/-- **C0b.4-pre18: left idxMap inclusion (left endpoint).** -/
lemma SimplePredictable.mergedIdxMap_left_idx_le
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (j : Fin (H₁.mergedM H₂)) :
    H₁.partition (H₁.mergedIdxMap_left H₂ h_eq j).castSucc
      ≤ H₁.mergedπ H₂ j.castSucc :=
  (H₁.exists_mergedIdxMap_left H₂ h_eq j).choose_spec.1
/-- **C0b.4-pre19: left idxMap inclusion (right endpoint).** -/
lemma SimplePredictable.mergedIdxMap_left_idx_ge
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (j : Fin (H₁.mergedM H₂)) :
    H₁.mergedπ H₂ j.succ
      ≤ H₁.partition (H₁.mergedIdxMap_left H₂ h_eq j).succ :=
  (H₁.exists_mergedIdxMap_left H₂ h_eq j).choose_spec.2
/-- **C0b.4-pre20: right index map.** Mirror of `mergedIdxMap_left`. -/
noncomputable def SimplePredictable.mergedIdxMap_right
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (j : Fin (H₁.mergedM H₂)) : Fin H₂.N :=
  (H₁.exists_mergedIdxMap_right H₂ h_eq j).choose
/-- **C0b.4-pre21: right idxMap inclusion (left endpoint).** -/
lemma SimplePredictable.mergedIdxMap_right_idx_le
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (j : Fin (H₁.mergedM H₂)) :
    H₂.partition (H₁.mergedIdxMap_right H₂ h_eq j).castSucc
      ≤ H₁.mergedπ H₂ j.castSucc :=
  (H₁.exists_mergedIdxMap_right H₂ h_eq j).choose_spec.1
/-- **C0b.4-pre22: right idxMap inclusion (right endpoint).** -/
lemma SimplePredictable.mergedIdxMap_right_idx_ge
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (j : Fin (H₁.mergedM H₂)) :
    H₁.mergedπ H₂ j.succ
      ≤ H₂.partition (H₁.mergedIdxMap_right H₂ h_eq j).succ :=
  (H₁.exists_mergedIdxMap_right H₂ h_eq j).choose_spec.2
/-- **C0b.4: common refinement of `H₁` (the left input).** Refine
`H₁` onto the merged partition `mergedπ`, using `mergedIdxMap_left`
to map merged tiles back to `H₁`-tiles. The resulting SimplePredictable
has `N = H₁.mergedM H₂`, partition `mergedπ`, and `ξ_j = H₁.ξ (idxMap j)`. -/
noncomputable def SimplePredictable.commonRefinement_left
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N)) :
    SimplePredictable Ω T :=
  H₁.refine (H₁.mergedM H₂) (H₁.mergedπ H₂)
    ((_root_.Prove2MeSourceProof.h_3281419cf2ade5797eb4da52 H₁) H₂)
    ((_root_.Prove2MeSourceProof.h_04cf3c59e383c3e0f39e729b H₁) H₂ h_eq)
    (H₁.mergedπ_strictMono H₂)
    (H₁.mergedIdxMap_left H₂ h_eq)
    (H₁.mergedIdxMap_left_idx_le H₂ h_eq)
    (H₁.mergedIdxMap_left_idx_ge H₂ h_eq)
/-- **C0b.4: common refinement of `H₂` (the right input).** Mirror of
`commonRefinement_left`, refining `H₂` onto the same `mergedπ`. The
two refinements share `N` and `partition` but differ in `ξ`. -/
noncomputable def SimplePredictable.commonRefinement_right
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N)) :
    SimplePredictable Ω T :=
  H₂.refine (H₁.mergedM H₂) (H₁.mergedπ H₂)
    ((_root_.Prove2MeSourceProof.h_3281419cf2ade5797eb4da52 H₁) H₂)
    (h_eq ▸ (_root_.Prove2MeSourceProof.h_04cf3c59e383c3e0f39e729b H₁) H₂ h_eq)
    (H₁.mergedπ_strictMono H₂)
    (H₁.mergedIdxMap_right H₂ h_eq)
    (H₁.mergedIdxMap_right_idx_le H₂ h_eq)
    (H₁.mergedIdxMap_right_idx_ge H₂ h_eq)
/-- **C0b.5: compatibility of the two common refinements.** They have
the same `N` (both equal to `mergedM`) and the same `partition` function
(both equal to `mergedπ`). This is what allows pointwise subtraction
of their `ξ` values to form `sub_on_common`. -/
lemma SimplePredictable.commonRefinement_compat
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N)) :
    (H₁.commonRefinement_left H₂ h_eq).N
        = (H₁.commonRefinement_right H₂ h_eq).N
      ∧ HEq (H₁.commonRefinement_left H₂ h_eq).partition
            (H₁.commonRefinement_right H₂ h_eq).partition := by
  refine ⟨rfl, HEq.rfl⟩
/-- **C0b.6: subtraction on common refinement.** Given two
SimplePredictables sharing endpoint, the difference SimplePredictable
on the common refinement: same partition (`mergedπ`), with
`ξ_j ω = H₁.ξ (idxMap_left j) ω - H₂.ξ (idxMap_right j) ω`.

Boundedness uses `abs_sub` (`|a-b| ≤ |a|+|b|`) with the sum of bounds.
Measurability uses `Measurable.sub`. -/
noncomputable def SimplePredictable.sub_on_common
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N)) :
    SimplePredictable Ω T where
  N := H₁.mergedM H₂
  partition := H₁.mergedπ H₂
  partition_zero := (_root_.Prove2MeSourceProof.h_3281419cf2ade5797eb4da52 H₁) H₂
  partition_le_T := ((_root_.Prove2MeSourceProof.h_04cf3c59e383c3e0f39e729b H₁) H₂ h_eq) ▸ H₁.partition_le_T
  partition_strictMono := H₁.mergedπ_strictMono H₂
  ξ := fun j ω => H₁.ξ (H₁.mergedIdxMap_left H₂ h_eq j) ω
    - H₂.ξ (H₁.mergedIdxMap_right H₂ h_eq j) ω
  ξ_bounded := fun j => by
    obtain ⟨C₁, hC₁⟩ := H₁.ξ_bounded (H₁.mergedIdxMap_left H₂ h_eq j)
    obtain ⟨C₂, hC₂⟩ := H₂.ξ_bounded (H₁.mergedIdxMap_right H₂ h_eq j)
    exact ⟨C₁ + C₂, fun ω =>
      (abs_sub _ _).trans (add_le_add (hC₁ ω) (hC₂ ω))⟩
  ξ_measurable := fun j =>
    (H₁.ξ_measurable _).sub (H₂.ξ_measurable _)
end LevyStochCalc.Brownian.Ito


