-- Prove2me | Definitions.Def_SourceProof_77343081f4784a6d686f59fe
-- name    : SourceProof_77343081f4784a6d686f59fe
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:30:12.504635+00:00
-- url     : https://prove2.me/theorems/1545285f-36b1-453f-b7c5-ff9499d9a746
-- title:
--   LevyStochCalc source module: SourceProof_77343081f4784a6d686f59fe
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_eLpNorm_two_right_tendsto` comes from the `LevyStochCalc.Brownian.ItoL2CompletionQuadVar` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionQuadVar_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionQuadVar_F001
import Definitions.Def_SourceProof_199d6571e2e85cd1e6522226
import Definitions.Def_SourceProof_a11eee7d83378555a816acd3

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

theorem _root_.Prove2MeSourceProof.h_77343081f4784a6d686f59fe (s : ℝ) :
    Filter.Tendsto (fun r => MeasureTheory.eLpNorm
        (stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global r
          - stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global s) 2 P)
      (nhdsWithin s (Set.Ioi s)) (nhds 0) := by
  suffices hsq : Filter.Tendsto (fun r => ∫⁻ ω,
      (‖(LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global r
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas
          h_sq_int_global s) ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      (nhdsWithin s (Set.Ioi s)) (nhds 0) by
    have h2 := hsq.ennrpow_const ((1 : ℝ) / 2)
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h2
    refine h2.congr (fun r => ?_)
    rw [← LevyStochCalc.Brownian.Ito.eLpNorm_sq_eq_lintegral_nnnorm_sq, ← ENNReal.rpow_mul,
      show (2 : ℝ) * (1 / 2) = 1 from by norm_num, ENNReal.rpow_one]
  -- the squared increment
  rcases le_or_gt 0 s with hs | hs
  · -- s ≥ 0: orthogonality + isometry + horizon continuity
    have hFsq : ∀ {t : ℝ}, 0 ≤ t →
        ∫ ω, (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global t ω) ^ 2 ∂P
          = (∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) t, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal := by
      intro t ht
      have hb := LevyStochCalc.Brownian.Ito.lintegral_nnnorm_sq_eq_ofReal_integral
        (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t)
      rw [_root_.Prove2MeSourceProof.h_a11eee7d83378555a816acd3 W ℱ hℱ H h_meas h_progMeas
        h_sq_int_global ht] at hb
      rw [hb, ENNReal.toReal_ofReal (integral_nonneg (fun ω => sq_nonneg _))]
    have hincr : ∀ {r : ℝ}, s ≤ r →
        ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global r ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas
            h_sq_int_global s ω‖₊ : ℝ≥0∞) ^ 2 ∂P
          = ENNReal.ofReal
            ((∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) r, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal
              - (∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) s, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal) := by
      intro r hsr
      rw [LevyStochCalc.Brownian.Ito.lintegral_nnnorm_sq_eq_ofReal_integral
        (g := fun ω => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global r ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global s ω)
        ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global r).sub
          (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global s))]
      congr 1
      rw [_root_.Prove2MeSourceProof.h_410f74bc0d5bdc6969bf4ac5
        (_root_.Prove2MeSourceProof.h_199d6571e2e85cd1e6522226 W ℱ hℱ H h_meas h_progMeas h_sq_int_global)
        (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global s)
        (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global r) hsr,
        hFsq (le_trans hs hsr), hFsq hs]
    -- the toReal-difference → 0
    have hcont : Filter.Tendsto (fun r =>
        ((∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) r, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal
          - (∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) s, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal))
        (nhdsWithin s (Set.Ioi s)) (nhds 0) := by
      have hfin_s : ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) s, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤ :=
        ne_top_of_le_ne_top (h_sq_int_global (s + 1) (by linarith)).ne
          (MeasureTheory.lintegral_mono (fun ω =>
            lintegral_mono_set (Set.Icc_subset_Icc_right (by linarith))))
      have h0 := (ENNReal.tendsto_toReal hfin_s).comp
        (LevyStochCalc.Brownian.Ito.horizon_lintegral_right_tendsto H h_meas h_sq_int_global hs)
      have h1 := h0.sub_const
        ((∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) s, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal)
      rw [sub_self] at h1
      exact h1
    have hof := (ENNReal.continuous_ofReal.tendsto 0).comp hcont
    rw [ENNReal.ofReal_zero] at hof
    refine hof.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hincr (le_of_lt hr)).symm
  · -- s < 0: eventually zero
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Ioo_mem_nhdsGT hs] with r hr
    symm
    rw [← MeasureTheory.lintegral_zero (μ := P)]
    refine lintegral_congr_ae ?_
    filter_upwards [LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_zero_of_neg W ℱ hℱ H h_meas h_progMeas
        h_sq_int_global hr.2,
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_zero_of_neg W ℱ hℱ H h_meas h_progMeas h_sq_int_global hs]
      with ω hr0 hs0
    simp [hr0, hs0]
end MasterSequence

end LevyStochCalc.Brownian.Ito


