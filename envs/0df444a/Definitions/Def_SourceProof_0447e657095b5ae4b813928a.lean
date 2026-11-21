-- Prove2me | Definitions.Def_SourceProof_0447e657095b5ae4b813928a
-- name    : SourceProof_0447e657095b5ae4b813928a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T15:46:20.800565+00:00
-- url     : https://prove2.me/theorems/50cab545-e922-4680-9bf1-b0a6b7c3adc7
-- title:
--   LevyStochCalc source module: SourceProof_0447e657095b5ae4b813928a
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.SimplePredictable.simpleIntegral_sub_on_common_intermediate` comes from the `LevyStochCalc.Brownian.SimplePredictableRefineCommon` module. The staged Lean declaration includes its source proof and dependency references.
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


theorem _root_.Prove2MeSourceProof.h_0447e657095b5ae4b813928a
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (t : ℝ) (ω : Ω) :
    simpleIntegral W (H₁.sub_on_common H₂ h_eq) t ω
      = simpleIntegral W H₁ t ω - simpleIntegral W H₂ t ω := by
  unfold LevyStochCalc.Brownian.Ito.simpleIntegral
  change (∑ j : Fin (H₁.mergedM H₂),
        (H₁.ξ (H₁.mergedIdxMap_left H₂ h_eq j) ω
          - H₂.ξ (H₁.mergedIdxMap_right H₂ h_eq j) ω)
        * (W.W (min (H₁.mergedπ H₂ j.succ) t) ω
            - W.W (min (H₁.mergedπ H₂ j.castSucc) t) ω))
      = LevyStochCalc.Brownian.Ito.simpleIntegral W H₁ t ω - LevyStochCalc.Brownian.Ito.simpleIntegral W H₂ t ω
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  congr 1
  · have h_left := H₁.simpleIntegral_refine_intermediate W (H₁.mergedM H₂) (H₁.mergedπ H₂)
      ((_root_.Prove2MeSourceProof.h_3281419cf2ade5797eb4da52 H₁) H₂) ((_root_.Prove2MeSourceProof.h_04cf3c59e383c3e0f39e729b H₁) H₂ h_eq) (H₁.mergedπ_strictMono H₂)
      (H₁.mergedIdxMap_left H₂ h_eq) (H₁.mergedIdxMap_left_idx_le H₂ h_eq)
      (H₁.mergedIdxMap_left_idx_ge H₂ h_eq) (H₁.mergedπ_refines_left H₂) t ω
    rw [← h_left]
    exact Finset.sum_congr rfl (fun _ _ => rfl)
  · have h_right := H₂.simpleIntegral_refine_intermediate W (H₁.mergedM H₂) (H₁.mergedπ H₂)
      ((_root_.Prove2MeSourceProof.h_3281419cf2ade5797eb4da52 H₁) H₂) (h_eq ▸ (_root_.Prove2MeSourceProof.h_04cf3c59e383c3e0f39e729b H₁) H₂ h_eq)
      (H₁.mergedπ_strictMono H₂)
      (H₁.mergedIdxMap_right H₂ h_eq) (H₁.mergedIdxMap_right_idx_le H₂ h_eq)
      (H₁.mergedIdxMap_right_idx_ge H₂ h_eq) (H₁.mergedπ_refines_right H₂) t ω
    rw [← h_right]
    exact Finset.sum_congr rfl (fun _ _ => rfl)
end LevyStochCalc.Brownian.Ito


