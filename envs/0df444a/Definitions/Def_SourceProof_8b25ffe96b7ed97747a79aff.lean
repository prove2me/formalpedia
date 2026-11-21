-- Prove2me | Definitions.Def_SourceProof_8b25ffe96b7ed97747a79aff
-- name    : SourceProof_8b25ffe96b7ed97747a79aff
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T15:46:44.954887+00:00
-- url     : https://prove2.me/theorems/1ce94c6f-2fb9-4bc8-b202-c0d8abd3fc1d
-- title:
--   LevyStochCalc source module: SourceProof_8b25ffe96b7ed97747a79aff
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.SimplePredictable.simpleIntegral_sub_on_common` comes from the `LevyStochCalc.Brownian.SimplePredictableRefineCommon` module. The staged Lean declaration includes its source proof and dependency references.
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


theorem _root_.Prove2MeSourceProof.h_8b25ffe96b7ed97747a79aff
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (ω : Ω) :
    simpleIntegral W (H₁.sub_on_common H₂ h_eq) T ω
      = simpleIntegral W H₁ T ω - simpleIntegral W H₂ T ω := by
  rw [LevyStochCalc.Brownian.Ito.simpleIntegral_eq_sum]
  change (∑ j : Fin (H₁.mergedM H₂),
        (H₁.ξ (H₁.mergedIdxMap_left H₂ h_eq j) ω
          - H₂.ξ (H₁.mergedIdxMap_right H₂ h_eq j) ω)
        * (W.W (H₁.mergedπ H₂ j.succ) ω - W.W (H₁.mergedπ H₂ j.castSucc) ω))
      = LevyStochCalc.Brownian.Ito.simpleIntegral W H₁ T ω - LevyStochCalc.Brownian.Ito.simpleIntegral W H₂ T ω
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  congr 1
  · -- LHS sum = simpleIntegral W H₁ T ω
    have h_left := H₁.simpleIntegral_refine W (H₁.mergedM H₂) (H₁.mergedπ H₂)
      ((_root_.Prove2MeSourceProof.h_3281419cf2ade5797eb4da52 H₁) H₂) ((_root_.Prove2MeSourceProof.h_04cf3c59e383c3e0f39e729b H₁) H₂ h_eq) (H₁.mergedπ_strictMono H₂)
      (H₁.mergedIdxMap_left H₂ h_eq) (H₁.mergedIdxMap_left_idx_le H₂ h_eq)
      (H₁.mergedIdxMap_left_idx_ge H₂ h_eq) (H₁.mergedπ_refines_left H₂) ω
    rw [← h_left, LevyStochCalc.Brownian.Ito.simpleIntegral_eq_sum]
    exact Finset.sum_congr rfl (fun _ _ => rfl)
  · -- RHS sum = simpleIntegral W H₂ T ω
    have h_right := H₂.simpleIntegral_refine W (H₁.mergedM H₂) (H₁.mergedπ H₂)
      ((_root_.Prove2MeSourceProof.h_3281419cf2ade5797eb4da52 H₁) H₂) (h_eq ▸ (_root_.Prove2MeSourceProof.h_04cf3c59e383c3e0f39e729b H₁) H₂ h_eq)
      (H₁.mergedπ_strictMono H₂)
      (H₁.mergedIdxMap_right H₂ h_eq) (H₁.mergedIdxMap_right_idx_le H₂ h_eq)
      (H₁.mergedIdxMap_right_idx_ge H₂ h_eq) (H₁.mergedπ_refines_right H₂) ω
    rw [← h_right, LevyStochCalc.Brownian.Ito.simpleIntegral_eq_sum]
    exact Finset.sum_congr rfl (fun _ _ => rfl)
end LevyStochCalc.Brownian.Ito


