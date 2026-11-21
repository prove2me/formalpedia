-- Prove2me | Definitions.Def_SourceProof_04cf3c59e383c3e0f39e729b
-- name    : SourceProof_04cf3c59e383c3e0f39e729b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T15:06:15.249364+00:00
-- url     : https://prove2.me/theorems/1b5b8c05-16d9-4671-8f23-28bb172e765a
-- title:
--   LevyStochCalc source module: SourceProof_04cf3c59e383c3e0f39e729b
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.SimplePredictable.mergedπ_last` comes from the `LevyStochCalc.Brownian.SimplePredictableRefineCommon` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineCommon_F001

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


theorem _root_.Prove2MeSourceProof.h_04cf3c59e383c3e0f39e729b
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N)) :
    H₁.mergedπ H₂ (Fin.last (H₁.mergedM H₂)) =
      H₁.partition (Fin.last H₁.N) := by
  unfold LevyStochCalc.Brownian.Ito.SimplePredictable.mergedπ
  have hz : (0 : ℕ) < H₁.mergedM H₂ + 1 := Nat.succ_pos _
  have h_last_eq : (Fin.last (H₁.mergedM H₂) : Fin (H₁.mergedM H₂ + 1))
      = ⟨H₁.mergedM H₂ + 1 - 1, by omega⟩ := by
    apply Fin.ext; simp
  rw [h_last_eq]
  rw [Finset.orderEmbOfFin_last (H₁.mergedM_card_eq H₂) hz]
  -- Goal: max' (mergedPartitionPoints) ⋯ = H₁.partition (Fin.last H₁.N)
  have h_endpt_mem : H₁.partition (Fin.last H₁.N) ∈ H₁.mergedPartitionPoints H₂ :=
    H₁.partition_mem_mergedPartitionPoints_left H₂ (Fin.last H₁.N)
  apply le_antisymm
  · -- max' ≤ endpoint, since endpoint is an upper bound
    apply Finset.max'_le
    intro x hx
    exact H₁.mem_mergedPartitionPoints_le_endpoint H₂ h_eq hx
  · -- endpoint ≤ max', since endpoint is a member
    exact Finset.le_max' _ _ h_endpt_mem
end LevyStochCalc.Brownian.Ito


