-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineCommon_F000
-- name    : LevyStochCalc_Brownian_SimplePredictableRefineCommon_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T08:12:45.304183+00:00
-- url     : https://prove2.me/theorems/c16710a8-7471-47a5-916d-c77ac866ff72
-- title:
--   Source declarations: LevyStochCalc.Brownian.SimplePredictableRefineCommon
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.SimplePredictableRefineCommon. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineInvariance_F002
import Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineInvariance_F003
import Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineInvariance_F004

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

/-- **C0b.4-pre1: Merged partition points.** The union of the two
SimplePredictables' partition images, as a `Finset ℝ`. The cardinality
of this Finset will become `M + 1` for the common refinement. -/
noncomputable def SimplePredictable.mergedPartitionPoints
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T) : Finset ℝ :=
  (Finset.univ.image H₁.partition) ∪ (Finset.univ.image H₂.partition)
/-- **C0b.4-pre2: `0` is in the merged set.** Both partitions start at
`0` (`partition_zero`), so `0 = H₁.partition 0` is a member. -/
lemma SimplePredictable.zero_mem_mergedPartitionPoints
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T) :
    (0 : ℝ) ∈ H₁.mergedPartitionPoints H₂ := by
  rw [SimplePredictable.mergedPartitionPoints]
  exact Finset.mem_union.mpr (Or.inl
    (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, H₁.partition_zero⟩))
/-- **C0b.4-pre3a: every `H₁.partition i` is in the merged set.** -/
lemma SimplePredictable.partition_mem_mergedPartitionPoints_left
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T) (i : Fin (H₁.N + 1)) :
    H₁.partition i ∈ H₁.mergedPartitionPoints H₂ := by
  rw [SimplePredictable.mergedPartitionPoints]
  exact Finset.mem_union.mpr (Or.inl
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
/-- **C0b.4-pre3b: every `H₂.partition i` is in the merged set.** -/
lemma SimplePredictable.partition_mem_mergedPartitionPoints_right
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T) (i : Fin (H₂.N + 1)) :
    H₂.partition i ∈ H₁.mergedPartitionPoints H₂ := by
  rw [SimplePredictable.mergedPartitionPoints]
  exact Finset.mem_union.mpr (Or.inr
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
/-- **C0b.4-pre4: number of tiles in the common refinement.** Equals
the cardinality of the merged set minus one. -/
noncomputable def SimplePredictable.mergedM
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T) : ℕ :=
  (H₁.mergedPartitionPoints H₂).card - 1
/-- **C0b.4-pre5: cardinality vs. `mergedM`.** Since `0` is in the
merged set, the cardinality is at least 1, so
`card = mergedM + 1` (rearranging `mergedM = card - 1`). -/
lemma SimplePredictable.mergedM_card_eq
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T) :
    (H₁.mergedPartitionPoints H₂).card = H₁.mergedM H₂ + 1 := by
  have h_pos : 0 < (H₁.mergedPartitionPoints H₂).card :=
    Finset.card_pos.mpr ⟨0, H₁.zero_mem_mergedPartitionPoints H₂⟩
  rw [SimplePredictable.mergedM]
  omega
/-- **C0b.4-pre6: the common-refinement partition function.** The
strictly-monotone enumeration of the merged Finset, with domain
`Fin (mergedM + 1)`. -/
noncomputable def SimplePredictable.mergedπ
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T) :
    Fin (H₁.mergedM H₂ + 1) → ℝ :=
  fun k => (H₁.mergedPartitionPoints H₂).orderEmbOfFin (H₁.mergedM_card_eq H₂) k
/-- **C0b.4-pre7: `mergedπ` is strictly monotone.** Direct from
`orderEmbOfFin` being an order embedding. -/
lemma SimplePredictable.mergedπ_strictMono
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T) :
    StrictMono (H₁.mergedπ H₂) :=
  ((H₁.mergedPartitionPoints H₂).orderEmbOfFin (H₁.mergedM_card_eq H₂)).strictMono
/-- **C0b.4-pre8: every partition value is non-negative.** Since
`partition 0 = 0` and `partition` is strictly monotone, every later
value dominates `0`. -/
lemma SimplePredictable.partition_nonneg
    {T : ℝ} (H : SimplePredictable Ω T) (i : Fin (H.N + 1)) :
    0 ≤ H.partition i := by
  rw [← H.partition_zero]
  exact H.partition_strictMono.monotone (Fin.zero_le i)
/-- **C0b.4-pre9: every element of the merged set is non-negative.** -/
lemma SimplePredictable.mem_mergedPartitionPoints_nonneg
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T) {x : ℝ}
    (hx : x ∈ H₁.mergedPartitionPoints H₂) : 0 ≤ x := by
  rcases Finset.mem_union.mp hx with h | h
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    rw [← hi]; exact H₁.partition_nonneg i
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    rw [← hi]; exact H₂.partition_nonneg i
end LevyStochCalc.Brownian.Ito


