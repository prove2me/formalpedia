-- Prove2me | Definitions.Def_SourceProof_cf6869ddf4a1bc9e1db02f28
-- name    : SourceProof_cf6869ddf4a1bc9e1db02f28
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T15:47:23.036334+00:00
-- url     : https://prove2.me/theorems/1ad600b1-88a6-4307-a0fd-0cc0f21a0a56
-- title:
--   LevyStochCalc source module: SourceProof_cf6869ddf4a1bc9e1db02f28
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.SimplePredictable.eval_sub_on_common` comes from the `LevyStochCalc.Brownian.SimplePredictableRefineCommon` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineCommon_F002
import Definitions.Def_SourceProof_c5e7e13c0417ce042a8b56ea

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


theorem _root_.Prove2MeSourceProof.h_cf6869ddf4a1bc9e1db02f28
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (s : ℝ) (ω : Ω) :
    (H₁.sub_on_common H₂ h_eq).eval s ω
      = H₁.eval s ω - H₂.eval s ω := by
  rw [← (_root_.Prove2MeSourceProof.h_c5e7e13c0417ce042a8b56ea H₁) (H₁.mergedM H₂) (H₁.mergedπ H₂)
        ((_root_.Prove2MeSourceProof.h_3281419cf2ade5797eb4da52 H₁) H₂) ((_root_.Prove2MeSourceProof.h_04cf3c59e383c3e0f39e729b H₁) H₂ h_eq)
        (H₁.mergedπ_strictMono H₂) (H₁.mergedIdxMap_left H₂ h_eq)
        (H₁.mergedIdxMap_left_idx_le H₂ h_eq)
        (H₁.mergedIdxMap_left_idx_ge H₂ h_eq) s ω]
  rw [← (_root_.Prove2MeSourceProof.h_c5e7e13c0417ce042a8b56ea H₂) (H₁.mergedM H₂) (H₁.mergedπ H₂)
        ((_root_.Prove2MeSourceProof.h_3281419cf2ade5797eb4da52 H₁) H₂) (h_eq ▸ (_root_.Prove2MeSourceProof.h_04cf3c59e383c3e0f39e729b H₁) H₂ h_eq)
        (H₁.mergedπ_strictMono H₂) (H₁.mergedIdxMap_right H₂ h_eq)
        (H₁.mergedIdxMap_right_idx_le H₂ h_eq)
        (H₁.mergedIdxMap_right_idx_ge H₂ h_eq) s ω]
  unfold LevyStochCalc.Brownian.Ito.SimplePredictable.eval
  change (∑ j : Fin (H₁.mergedM H₂),
        if H₁.mergedπ H₂ j.castSucc < s ∧ s ≤ H₁.mergedπ H₂ j.succ
        then (H₁.ξ (H₁.mergedIdxMap_left H₂ h_eq j) ω
              - H₂.ξ (H₁.mergedIdxMap_right H₂ h_eq j) ω)
        else 0)
      = (∑ j : Fin (H₁.mergedM H₂),
          if H₁.mergedπ H₂ j.castSucc < s ∧ s ≤ H₁.mergedπ H₂ j.succ
          then H₁.ξ (H₁.mergedIdxMap_left H₂ h_eq j) ω else 0)
        - (∑ j : Fin (H₁.mergedM H₂),
          if H₁.mergedπ H₂ j.castSucc < s ∧ s ≤ H₁.mergedπ H₂ j.succ
          then H₂.ξ (H₁.mergedIdxMap_right H₂ h_eq j) ω else 0)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h_cond : H₁.mergedπ H₂ j.castSucc < s ∧ s ≤ H₁.mergedπ H₂ j.succ
  · simp [h_cond]
  · simp [h_cond]
end LevyStochCalc.Brownian.Ito


