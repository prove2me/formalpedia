-- Prove2me | Definitions.Def_SourceProof_a11eee7d83378555a816acd3
-- name    : SourceProof_a11eee7d83378555a816acd3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:28:35.100114+00:00
-- url     : https://prove2.me/theorems/f1a320eb-386b-4cf6-984d-7cbb9c212ff9
-- title:
--   LevyStochCalc source module: SourceProof_a11eee7d83378555a816acd3
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_lintegral_sq` comes from the `LevyStochCalc.Brownian.ItoL2CompletionQuadVar` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_39285c9e8cb91346b858af97
import Definitions.Def_SourceProof_7aea30f549f53f05062f1907

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: isometry, right continuity and quadratic variation

The `L²`-isometry `∫⁻ ‖stochasticIntegralBrownian T‖₊² = ∫⁻ ∫⁻_{[0, T]} ‖H‖₊²`,
membership of the process in `L²(P)`, right `L²`-continuity of its time slices and
the resulting martingale property with respect to the right-continuation `ℱ₊` of
`ℱ`, and the compensator `∫_{[0, t]} (H ω u)² du` with the `ℱ`-martingale property
of the compensated square.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

section MasterSequence

variable
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

include hℱ in

theorem _root_.Prove2MeSourceProof.h_a11eee7d83378555a816acd3 {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas
      h_sq_int_global t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  rcases lt_or_eq_of_le ht with ht' | ht'
  · exact _root_.Prove2MeSourceProof.h_7aea30f549f53f05062f1907 W ℱ hℱ H h_meas h_progMeas h_sq_int_global ht'
  · subst ht'
    rw [lintegral_congr_ae (by
      filter_upwards [_root_.Prove2MeSourceProof.h_39285c9e8cb91346b858af97 W ℱ hℱ H h_meas h_progMeas
        h_sq_int_global (le_refl (0:ℝ))] with ω hω; rw [hω]; simp : _ =ᵐ[P] fun _ => (0:ℝ≥0∞))]
    rw [MeasureTheory.lintegral_zero]
    symm
    rw [← MeasureTheory.lintegral_zero (μ := P)]
    refine lintegral_congr (fun ω => ?_)
    rw [MeasureTheory.setLIntegral_measure_zero _ _ (by simp)]
end MasterSequence

end LevyStochCalc.Brownian.Ito


