-- Prove2me | Definitions.Def_SourceProof_3281419cf2ade5797eb4da52
-- name    : SourceProof_3281419cf2ade5797eb4da52
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T12:24:20.537006+00:00
-- url     : https://prove2.me/theorems/f189e337-69d5-45c5-ab97-0b9de1326785
-- title:
--   LevyStochCalc source module: SourceProof_3281419cf2ade5797eb4da52
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.SimplePredictable.mergedπ_zero` comes from the `LevyStochCalc.Brownian.SimplePredictableRefineCommon` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineCommon_F000

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


theorem _root_.Prove2MeSourceProof.h_3281419cf2ade5797eb4da52
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T) :
    H₁.mergedπ H₂ 0 = 0 := by
  unfold LevyStochCalc.Brownian.Ito.SimplePredictable.mergedπ
  have hz : (0 : ℕ) < H₁.mergedM H₂ + 1 := Nat.succ_pos _
  have h_zero_eq : (0 : Fin (H₁.mergedM H₂ + 1)) = ⟨0, hz⟩ := rfl
  rw [h_zero_eq]
  rw [Finset.orderEmbOfFin_zero (H₁.mergedM_card_eq H₂) hz]
  -- Now goal: min' (mergedPartitionPoints) ⋯ = 0
  have h_zero_mem : (0 : ℝ) ∈ H₁.mergedPartitionPoints H₂ :=
    H₁.zero_mem_mergedPartitionPoints H₂
  apply le_antisymm
  · exact Finset.min'_le _ _ h_zero_mem
  · exact H₁.mem_mergedPartitionPoints_nonneg H₂
      (Finset.min'_mem _ _)
end LevyStochCalc.Brownian.Ito


