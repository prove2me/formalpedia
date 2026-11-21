-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineCommon_F003
-- name    : LevyStochCalc_Brownian_SimplePredictableRefineCommon_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T15:10:04.404189+00:00
-- url     : https://prove2.me/theorems/df740864-20eb-40f2-8092-25d65bac08ab
-- title:
--   Source declarations: LevyStochCalc.Brownian.SimplePredictableRefineCommon
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.SimplePredictableRefineCommon. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineCommon_F002

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

/-- **C0b.8-pre: adaptedness of `sub_on_common`.** If both inputs are
adapted to a filtration `ℱ`, so is `sub_on_common`. The
proof: for each merged tile `j`, the input adaptedness gives StronglyMeas
at `H_k.partition (idxMap_k j).castSucc`. By `Filtration.mono` and
`mergedIdxMap_k_idx_le` (which says `H_k.partition (idxMap_k j).castSucc
≤ mergedπ j.castSucc`), this upgrades to StronglyMeas at the merged
partition point. The difference is StronglyMeas via `StronglyMeasurable.sub`. -/
lemma SimplePredictable.sub_on_common_adapt
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (h_adapt₁ : ∀ i : Fin H₁.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H₁.partition i.castSucc)) (H₁.ξ i))
    (h_adapt₂ : ∀ i : Fin H₂.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H₂.partition i.castSucc)) (H₂.ξ i)) :
    ∀ j : Fin (H₁.sub_on_common H₂ h_eq).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ ((H₁.sub_on_common H₂ h_eq).partition j.castSucc))
        ((H₁.sub_on_common H₂ h_eq).ξ j) := by
  intro j
  have h_mono₁ := ℱ.mono
    (H₁.mergedIdxMap_left_idx_le H₂ h_eq j)
  have h_mono₂ := ℱ.mono
    (H₁.mergedIdxMap_right_idx_le H₂ h_eq j)
  have h₁ := (h_adapt₁ (H₁.mergedIdxMap_left H₂ h_eq j)).mono h_mono₁
  have h₂ := (h_adapt₂ (H₁.mergedIdxMap_right H₂ h_eq j)).mono h_mono₂
  exact h₁.sub h₂
end LevyStochCalc.Brownian.Ito


