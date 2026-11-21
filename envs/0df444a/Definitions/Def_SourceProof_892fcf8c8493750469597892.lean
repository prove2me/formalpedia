-- Prove2me | Definitions.Def_SourceProof_892fcf8c8493750469597892
-- name    : SourceProof_892fcf8c8493750469597892
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:00:39.672567+00:00
-- url     : https://prove2.me/theorems/21450cf9-0277-4e81-b623-35b5a37c36d1
-- title:
--   LevyStochCalc source module: SourceProof_892fcf8c8493750469597892
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.SimplePredictable.eval_mul_on_common` comes from the `LevyStochCalc.Brownian.ItoAlgebraProduct` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraProduct_F000
import Definitions.Def_SourceProof_c5e7e13c0417ce042a8b56ea

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Products of simple integrands and elementary integrals against a process

Two simple integrands with a common final partition point multiply to a simple integrand carried
on their common refinement, whose evaluation is the pointwise product of the evaluations and
whose adaptedness is inherited; summing the increments of the elementary integral of one against
the coefficients of the other is the elementary integral of that product, and the difference
between an elementary integral and an `L²` Itô integral obeys the Itô isometry.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.Prove2MeSourceProof.h_892fcf8c8493750469597892
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (s : ℝ) (ω : Ω) :
    (H₁.mul_on_common H₂ h_eq).eval s ω = H₁.eval s ω * H₂.eval s ω := by
  have hl := (_root_.Prove2MeSourceProof.h_c5e7e13c0417ce042a8b56ea H₁) (H₁.mergedM H₂) (H₁.mergedπ H₂) ((_root_.Prove2MeSourceProof.h_3281419cf2ade5797eb4da52 H₁) H₂)
    ((_root_.Prove2MeSourceProof.h_04cf3c59e383c3e0f39e729b H₁) H₂ h_eq) (H₁.mergedπ_strictMono H₂)
    (H₁.mergedIdxMap_left H₂ h_eq)
    (H₁.mergedIdxMap_left_idx_le H₂ h_eq) (H₁.mergedIdxMap_left_idx_ge H₂ h_eq) s ω
  have hr := (_root_.Prove2MeSourceProof.h_c5e7e13c0417ce042a8b56ea H₂) (H₁.mergedM H₂) (H₁.mergedπ H₂) ((_root_.Prove2MeSourceProof.h_3281419cf2ade5797eb4da52 H₁) H₂)
    (h_eq ▸ (_root_.Prove2MeSourceProof.h_04cf3c59e383c3e0f39e729b H₁) H₂ h_eq) (H₁.mergedπ_strictMono H₂)
    (H₁.mergedIdxMap_right H₂ h_eq)
    (H₁.mergedIdxMap_right_idx_le H₂ h_eq) (H₁.mergedIdxMap_right_idx_ge H₂ h_eq) s ω
  rw [LevyStochCalc.Brownian.Ito.SimplePredictable.eval] at hl hr ⊢
  change (∑ j : Fin (H₁.mergedM H₂),
      if H₁.mergedπ H₂ j.castSucc < s ∧ s ≤ H₁.mergedπ H₂ j.succ
        then H₁.ξ (H₁.mergedIdxMap_left H₂ h_eq j) ω
          * H₂.ξ (H₁.mergedIdxMap_right H₂ h_eq j) ω else 0)
    = H₁.eval s ω * H₂.eval s ω
  rw [← hl, ← hr]
  exact (LevyStochCalc.Brownian.Ito.sum_ite_mul_sum_ite (H₁.mergedπ_strictMono H₂) _ _ s).symm
section SimpleVsGeneral

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  {T₀ : ℝ} (G : SimplePredictable Ω T₀)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

end SimpleVsGeneral

end LevyStochCalc.Brownian.Ito


