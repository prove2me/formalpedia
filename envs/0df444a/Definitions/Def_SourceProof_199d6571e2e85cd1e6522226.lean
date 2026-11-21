-- Prove2me | Definitions.Def_SourceProof_199d6571e2e85cd1e6522226
-- name    : SourceProof_199d6571e2e85cd1e6522226
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:25:14.700102+00:00
-- url     : https://prove2.me/theorems/17b405e1-bd35-4971-97b6-28a53f4e07e8
-- title:
--   LevyStochCalc source module: SourceProof_199d6571e2e85cd1e6522226
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.martingale_stochasticIntegralBrownian` comes from the `LevyStochCalc.Brownian.ItoL2CompletionMaster` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionMaster_F003
import Definitions.Def_SourceProof_2554b195ead815ae5442020c
import Definitions.Def_SourceProof_7f016bcc8755267478a0d8f9

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: the master approximating sequence

The master sequence `masterApprox` of adapted simple predictable integrands on the
growing horizons `[0, n + 1]`, its Cauchy property in `L²(P)` uniformly on compact
time intervals, the limit `masterLp` and `stochasticIntegralBrownianLp` in
`Lp ℝ 2 P`, and the process `stochasticIntegralBrownian` together with its
adaptedness, vanishing on negative times and `ℱ`-martingale property.
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

theorem _root_.Prove2MeSourceProof.h_199d6571e2e85cd1e6522226 :
    MeasureTheory.Martingale (stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global)
      ℱ P := by
  refine _root_.Prove2MeSourceProof.h_7f016bcc8755267478a0d8f9
    (M := fun n t => LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n) t)
    (fun n => _root_.Prove2MeSourceProof.h_79c2c57f6aeff6dbd6853f31 W ℱ hℱ
      (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n)
      (LevyStochCalc.Brownian.Ito.masterApprox_adapt ℱ H h_meas h_progMeas h_sq_int_global n))
    (fun n t => (_root_.Prove2MeSourceProof.h_79c2c57f6aeff6dbd6853f31 W ℱ hℱ
      (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n)
      (LevyStochCalc.Brownian.Ito.masterApprox_adapt ℱ H h_meas h_progMeas h_sq_int_global n)).integrable t)
    (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H h_meas h_progMeas h_sq_int_global)
    (fun t => ((MeasureTheory.Lp.memLp _).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).congr
      (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_eq W ℱ hℱ H h_meas h_progMeas h_sq_int_global t).symm)
    (fun t => ?_)
  rcases le_or_gt 0 t with ht | ht
  · refine LevyStochCalc.Brownian.Ito.tendsto_eLpNorm_one_of_eLpNorm_two (fun n => ?_)
      (_root_.Prove2MeSourceProof.h_2554b195ead815ae5442020c W ℱ hℱ H h_meas h_progMeas h_sq_int_global ht)
    refine (Measurable.aestronglyMeasurable ?_).sub
      (((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H h_meas h_progMeas
        h_sq_int_global t).mono
        (ℱ.le t)).aestronglyMeasurable)
    unfold LevyStochCalc.Brownian.Ito.simpleIntegral
    refine Finset.measurable_sum _ (fun i _ => ?_)
    exact ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).ξ_measurable i).mul
      ((W.measurable_eval _).sub (W.measurable_eval _))
  · have hzero : ∀ n, MeasureTheory.eLpNorm
        ((fun t' => LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n) t') t
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global t) 1 P = 0 := by
      intro n
      have hfae : ((fun t' => LevyStochCalc.Brownian.Ito.simpleIntegral W
            (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n) t') t
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global t) =ᵐ[P] 0 := by
        filter_upwards [LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_zero_of_neg W ℱ hℱ H h_meas h_progMeas
          h_sq_int_global ht] with ω hF
        simp only [Pi.sub_apply, Pi.zero_apply,
          LevyStochCalc.Brownian.Ito.simpleIntegral_eq_zero_of_nonpos W _ (le_of_lt ht) ω, hF, sub_zero]
      rw [MeasureTheory.eLpNorm_congr_ae hfae, MeasureTheory.eLpNorm_zero]
    simp only [hzero]
    exact tendsto_const_nhds
end MasterSequence

end LevyStochCalc.Brownian.Ito


