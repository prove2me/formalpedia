-- Prove2me | Definitions.Def_SourceProof_39285c9e8cb91346b858af97
-- name    : SourceProof_39285c9e8cb91346b858af97
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:26:39.059183+00:00
-- url     : https://prove2.me/theorems/d55aabf1-f638-455f-8b1a-25b1c8207d26
-- title:
--   LevyStochCalc source module: SourceProof_39285c9e8cb91346b858af97
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_zero_of_nonpos` comes from the `LevyStochCalc.Brownian.ItoL2CompletionQuadVar` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionQuadVar_F000
import Definitions.Def_SourceProof_2554b195ead815ae5442020c

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

theorem _root_.Prove2MeSourceProof.h_39285c9e8cb91346b858af97 {t : ℝ} (ht : t ≤ 0) :
    stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global t =ᵐ[P] 0 := by
  rcases lt_or_eq_of_le ht with ht' | ht'
  · exact LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_zero_of_neg W ℱ hℱ H h_meas h_progMeas h_sq_int_global ht'
  · subst ht'
    have h := _root_.Prove2MeSourceProof.h_2554b195ead815ae5442020c W ℱ hℱ H h_meas h_progMeas h_sq_int_global (le_refl (0 : ℝ))
    have hconst : ∀ n, MeasureTheory.eLpNorm
        (fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n) 0 ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global 0 ω) 2 P
        = MeasureTheory.eLpNorm
          (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global 0) 2 P := by
      intro n
      rw [← MeasureTheory.eLpNorm_neg
        (f := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global 0)]
      refine MeasureTheory.eLpNorm_congr_ae ?_
      filter_upwards with ω
      simp [LevyStochCalc.Brownian.Ito.simpleIntegral_eq_zero_of_nonpos W _ (le_refl (0 : ℝ)) ω]
    simp only [hconst] at h
    have hz : MeasureTheory.eLpNorm
        (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global 0) 2 P = 0 :=
      tendsto_nhds_unique tendsto_const_nhds h
    rwa [MeasureTheory.eLpNorm_eq_zero_iff
      (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global
        0).aestronglyMeasurable
      (by norm_num)] at hz
end MasterSequence

end LevyStochCalc.Brownian.Ito


