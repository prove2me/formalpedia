-- Prove2me | Definitions.Def_SourceProof_02639dd90be44822908c47b8
-- name    : SourceProof_02639dd90be44822908c47b8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T15:53:30.036469+00:00
-- url     : https://prove2.me/theorems/64d62bbd-6ab6-43ff-87b8-69872a3cbbb1
-- title:
--   LevyStochCalc source module: SourceProof_02639dd90be44822908c47b8
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.SimplePredictable.diff_isometry_simple` comes from the `LevyStochCalc.Brownian.SimplePredictableRefineCommon` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineCommon_F003
import Definitions.Def_SourceProof_8b25ffe96b7ed97747a79aff
import Definitions.Def_SourceProof_cf6869ddf4a1bc9e1db02f28

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


theorem _root_.Prove2MeSourceProof.h_02639dd90be44822908c47b8
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (hT : 0 < T) (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (h_adapt₁ : ∀ i : Fin H₁.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H₁.partition i.castSucc)) (H₁.ξ i))
    (h_adapt₂ : ∀ i : Fin H₂.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H₂.partition i.castSucc)) (H₂.ξ i)) :
    ∫⁻ ω, (‖simpleIntegral W H₁ T ω - simpleIntegral W H₂ T ω‖₊ : ℝ≥0∞) ^ 2
      ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H₁.eval s ω - H₂.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have h_LHS :
      ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W H₁ T ω - LevyStochCalc.Brownian.Ito.simpleIntegral W H₂ T ω‖₊
              : ℝ≥0∞) ^ 2 ∂P
        = ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (H₁.sub_on_common H₂ h_eq) T ω‖₊
              : ℝ≥0∞) ^ 2 ∂P := by
    refine MeasureTheory.lintegral_congr (fun ω => ?_)
    rw [_root_.Prove2MeSourceProof.h_8b25ffe96b7ed97747a79aff W H₁ H₂ h_eq ω]
  have h_RHS :
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H₁.eval s ω - H₂.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖((H₁.sub_on_common H₂ h_eq).eval s ω)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
        by
    refine MeasureTheory.lintegral_congr (fun ω => ?_)
    refine MeasureTheory.setLIntegral_congr_fun measurableSet_Icc
      (fun s _ => ?_)
    rw [_root_.Prove2MeSourceProof.h_cf6869ddf4a1bc9e1db02f28 H₁ H₂ h_eq s ω]
  rw [h_LHS, h_RHS]
  exact LevyStochCalc.Brownian.Ito.simpleIntegral_isometry W ℱ hℱ hT (H₁.sub_on_common H₂ h_eq)
    (LevyStochCalc.Brownian.Ito.SimplePredictable.sub_on_common_adapt ℱ H₁ H₂ h_eq h_adapt₁ h_adapt₂)
end LevyStochCalc.Brownian.Ito


