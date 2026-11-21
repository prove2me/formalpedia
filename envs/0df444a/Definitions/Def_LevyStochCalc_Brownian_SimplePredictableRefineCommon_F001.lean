-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineCommon_F001
-- name    : LevyStochCalc_Brownian_SimplePredictableRefineCommon_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T08:15:01.348186+00:00
-- url     : https://prove2.me/theorems/ab006294-43bf-4eda-be8c-96520b5f79db
-- title:
--   Source declarations: LevyStochCalc.Brownian.SimplePredictableRefineCommon
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.SimplePredictableRefineCommon. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
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

/-- **C0b.4-pre11: every element ≤ the (shared) endpoint.** Under
the assumption that both partitions end at the same point. -/
lemma SimplePredictable.mem_mergedPartitionPoints_le_endpoint
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    {x : ℝ} (hx : x ∈ H₁.mergedPartitionPoints H₂) :
    x ≤ H₁.partition (Fin.last H₁.N) := by
  rcases Finset.mem_union.mp hx with h | h
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    rw [← hi]
    exact H₁.partition_strictMono.monotone (Fin.le_last i)
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    rw [← hi]
    rw [h_eq]
    exact H₂.partition_strictMono.monotone (Fin.le_last i)
end LevyStochCalc.Brownian.Ito


