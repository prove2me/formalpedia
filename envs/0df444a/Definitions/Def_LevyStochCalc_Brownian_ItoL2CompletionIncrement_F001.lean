-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionIncrement_F001
-- name    : LevyStochCalc_Brownian_ItoL2CompletionIncrement_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T17:31:13.048502+00:00
-- url     : https://prove2.me/theorems/113e9198-f558-4e89-88d7-1abb681a1386
-- title:
--   LevyStochCalc source module: LevyStochCalc.Brownian.ItoL2CompletionIncrement
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Brownian.ItoL2CompletionIncrement in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionExistence_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionExistence_F001
import Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineCommon_F003
import Definitions.Def_SourceProof_0447e657095b5ae4b813928a
import Definitions.Def_SourceProof_07211334eb93145a1521a908
import Definitions.Def_SourceProof_cf6869ddf4a1bc9e1db02f28

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: increment expansions and the intermediate-time isometry

Diagonal and off-diagonal expectations of products of Brownian increments against
adapted weights, the Bochner expansion of the square of a simple integral clamped
at an intermediate time, and the isometry
`∫⁻ ‖simpleIntegral W H t‖₊² = ∫⁻ ∫⁻_{[0, t]} ‖H.eval‖₊²` it gives for every
intermediate time `t`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- **General-time difference isometry.** For adapted `H₁, H₂` sharing the endpoint
`T`, the `L²(P)`-norm² of the integral difference at *any* `t ≥ 0` equals the
`L²(λ⊗P)`-norm² of their eval difference over `[0, t]`. The `min (·) t`-clamped
analogue of `diff_isometry_simple`: rewrite the integral difference as the integral
of `sub_on_common` (`simpleIntegral_sub_on_common_intermediate`), apply the
intermediate-time isometry, and unfold `eval` of `sub_on_common`. This is the exact
isometry underlying both `L²`-Cauchy-at-each-`t` and cross-horizon consistency. -/
lemma simpleIntegral_intermediate_diff_isometry
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (h_adapt₁ : ∀ i : Fin H₁.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H₁.partition i.castSucc)) (H₁.ξ i))
    (h_adapt₂ : ∀ i : Fin H₂.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H₂.partition i.castSucc)) (H₂.ξ i))
    {t : ℝ} (ht_nn : 0 ≤ t) :
    ∫⁻ ω, (‖simpleIntegral W H₁ t ω - simpleIntegral W H₂ t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖H₁.eval s ω - H₂.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have hLHS : ∫⁻ ω, (‖simpleIntegral W H₁ t ω - simpleIntegral W H₂ t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖simpleIntegral W (H₁.sub_on_common H₂ h_eq) t ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    refine lintegral_congr (fun ω => ?_)
    rw [_root_.Prove2MeSourceProof.h_0447e657095b5ae4b813928a W H₁ H₂ h_eq t ω]
  rw [hLHS, _root_.Prove2MeSourceProof.h_07211334eb93145a1521a908 W ℱ hℱ (H₁.sub_on_common H₂ h_eq)
      (SimplePredictable.sub_on_common_adapt ℱ H₁ H₂ h_eq h_adapt₁ h_adapt₂) ht_nn]
  refine lintegral_congr (fun ω => ?_)
  refine MeasureTheory.setLIntegral_congr_fun measurableSet_Icc (fun s _ => ?_)
  rw [_root_.Prove2MeSourceProof.h_cf6869ddf4a1bc9e1db02f28 H₁ H₂ h_eq s ω]
end LevyStochCalc.Brownian.Ito


