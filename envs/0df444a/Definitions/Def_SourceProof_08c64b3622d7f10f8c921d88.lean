-- Prove2me | Definitions.Def_SourceProof_08c64b3622d7f10f8c921d88
-- name    : SourceProof_08c64b3622d7f10f8c921d88
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:31:43.493182+00:00
-- url     : https://prove2.me/theorems/61729dec-6a79-4b84-8e0a-3f5e6c278c0d
-- title:
--   LevyStochCalc source module: SourceProof_08c64b3622d7f10f8c921d88
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.martingale_rightCont_stochasticIntegralBrownian` comes from the `LevyStochCalc.Brownian.ItoL2CompletionQuadVar` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionQuadVar_F000
import Definitions.Def_SourceProof_199d6571e2e85cd1e6522226
import Definitions.Def_SourceProof_35156ff6984aa5b4b399bdef
import Definitions.Def_SourceProof_77343081f4784a6d686f59fe

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

theorem _root_.Prove2MeSourceProof.h_08c64b3622d7f10f8c921d88 :
    MeasureTheory.Martingale (stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global)
      ℱ.rightCont P := by
  refine _root_.Prove2MeSourceProof.h_35156ff6984aa5b4b399bdef
    (_root_.Prove2MeSourceProof.h_199d6571e2e85cd1e6522226 W ℱ hℱ H h_meas h_progMeas h_sq_int_global) (fun s => ?_)
  have hF_aesm : ∀ t, MeasureTheory.AEStronglyMeasurable
      (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global t) P :=
    fun t => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas
      h_sq_int_global t).aestronglyMeasurable
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (_root_.Prove2MeSourceProof.h_77343081f4784a6d686f59fe W ℱ hℱ H h_meas h_progMeas
      h_sq_int_global s)
    (Filter.Eventually.of_forall (fun r => bot_le))
    (Filter.Eventually.of_forall (fun r => MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le
      (by norm_num) ((hF_aesm r).sub (hF_aesm s))))
end MasterSequence

end LevyStochCalc.Brownian.Ito


