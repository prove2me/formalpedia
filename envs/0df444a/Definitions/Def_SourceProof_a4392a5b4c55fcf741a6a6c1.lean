-- Prove2me | Definitions.Def_SourceProof_a4392a5b4c55fcf741a6a6c1
-- name    : SourceProof_a4392a5b4c55fcf741a6a6c1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:28:56.29951+00:00
-- url     : https://prove2.me/theorems/30e9cfd5-1fd1-4791-a911-9478c1164d24
-- title:
--   LevyStochCalc source module: SourceProof_a4392a5b4c55fcf741a6a6c1
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.martingale_quadVar_stochasticIntegralBrownian` comes from the `LevyStochCalc.Brownian.ItoL2CompletionQuadVar` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionQuadVar_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionQuadVar_F002
import Definitions.Def_SourceProof_2554b195ead815ae5442020c
import Definitions.Def_SourceProof_6be12e51c788a72f4de041a3
import Definitions.Def_SourceProof_7f016bcc8755267478a0d8f9
import Definitions.Def_SourceProof_ad87eebc265310df7bf2d34e
import Definitions.Def_SourceProof_bdfc35f844d4c9ce2b4930ee
import Definitions.Def_SourceProof_c343f3fddeb9bb9bc3b8ffc2

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

include h_meas h_progMeas h_sq_int_global hℱ in

theorem _root_.Prove2MeSourceProof.h_a4392a5b4c55fcf741a6a6c1 :
    MeasureTheory.Martingale
      (fun t ω => (stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global t ω) ^ 2
        - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume)
      ℱ P := by
  set F := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global with hF
  have hAHint : ∀ t, MeasureTheory.Integrable
      (fun ω => ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) P := by
    intro t
    rcases le_or_gt 0 t with ht | ht
    · exact LevyStochCalc.Brownian.Ito.compensatorH_integrable H h_meas h_sq_int_global ht
    · have heq : (fun ω => ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) = fun _ => (0 : ℝ) := by
        funext ω; rw [Set.Icc_eq_empty (not_le.mpr ht)]; simp
      rw [heq]; exact MeasureTheory.integrable_const 0
  refine _root_.Prove2MeSourceProof.h_7f016bcc8755267478a0d8f9
    (M := fun n t ω =>
      (LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n) t ω) ^ 2
        - ∫ u in Set.Icc (0 : ℝ) t,
            ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval u ω) ^ 2 ∂volume)
    (fun n => _root_.Prove2MeSourceProof.h_ad87eebc265310df7bf2d34e W ℱ hℱ (LevyStochCalc.Brownian.Ito.master_horizon_pos n)
      (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n)
      (LevyStochCalc.Brownian.Ito.masterApprox_adapt ℱ H h_meas h_progMeas h_sq_int_global n))
    (fun n t => (_root_.Prove2MeSourceProof.h_ad87eebc265310df7bf2d34e W ℱ hℱ (LevyStochCalc.Brownian.Ito.master_horizon_pos n)
      (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n)
      (LevyStochCalc.Brownian.Ito.masterApprox_adapt ℱ H h_meas h_progMeas h_sq_int_global n)).integrable t)
    (fun t => ?_) (fun t => ?_) (fun t => ?_)
  · -- StronglyAdapted
    have hFsq : @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ t) (fun ω => (F t ω) ^ 2) := by
      simpa [pow_two, Pi.mul_def] using
        (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H h_meas h_progMeas
          h_sq_int_global t).mul
          (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H h_meas h_progMeas h_sq_int_global t)
    exact hFsq.sub (LevyStochCalc.Brownian.Ito.compensatorH_adapted ℱ H h_progMeas t)
  · -- integrability of the F-process at each `t`
    exact ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas
      h_sq_int_global t).integrable_sq).sub
      (hAHint t)
  · -- `L¹`-convergence of the simple compensated squares to the F-process
    rcases le_or_gt 0 t with ht | ht
    · have hX : Filter.Tendsto (fun n => MeasureTheory.eLpNorm
          (fun ω => (LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas
            h_sq_int_global n) t ω) ^ 2
            - (F t ω) ^ 2) 1 P) Filter.atTop (nhds 0) :=
        _root_.Prove2MeSourceProof.h_6be12e51c788a72f4de041a3
          (fun n => (Finset.measurable_sum _ (fun i _ =>
            ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).ξ_measurable i).mul
              ((W.measurable_eval _).sub (W.measurable_eval _)))).aemeasurable)
          (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas
            h_sq_int_global t).1.aemeasurable
          (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t).2.ne
          (_root_.Prove2MeSourceProof.h_2554b195ead815ae5442020c W ℱ hℱ H h_meas h_progMeas h_sq_int_global ht)
      have hY := _root_.Prove2MeSourceProof.h_bdfc35f844d4c9ce2b4930ee ℱ H h_meas h_progMeas h_sq_int_global ht
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (by simpa using hX.add hY)
        (Filter.Eventually.of_forall (fun n => bot_le))
        (Filter.Eventually.of_forall (fun n => ?_))
      have hXaesm : MeasureTheory.AEStronglyMeasurable
          (fun ω => (LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas
            h_sq_int_global n) t ω) ^ 2
            - (F t ω) ^ 2) P :=
        (((Finset.measurable_sum _ (fun i _ =>
          ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).ξ_measurable i).mul
            ((W.measurable_eval _).sub (W.measurable_eval _)))).pow_const
              2).aestronglyMeasurable).sub
          ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas
            h_sq_int_global t).1.aemeasurable.pow_const 2).aestronglyMeasurable
      have hAn_meas : Measurable (fun ω => ∫ u in Set.Icc (0 : ℝ) t,
          ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval u ω) ^ 2 ∂volume) := by
        rw [show (fun ω => ∫ u in Set.Icc (0 : ℝ) t,
              ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval u ω) ^ 2 ∂volume)
            = fun ω => ∑ i : Fin (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).N,
                (min ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).partition i.succ) t
                  - min ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).partition
                      i.castSucc) t)
                  * ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).ξ i ω) ^ 2 from
          funext (fun ω => _root_.Prove2MeSourceProof.h_c343f3fddeb9bb9bc3b8ffc2
            (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n) ω)]
        exact Finset.measurable_sum _ (fun i _ => measurable_const.mul
          (((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).ξ_measurable i).pow_const 2))
      have hYaesm : MeasureTheory.AEStronglyMeasurable
          (fun ω => (∫ u in Set.Icc (0 : ℝ) t,
              ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval u ω) ^ 2 ∂volume)
            - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) P :=
        hAn_meas.aestronglyMeasurable.sub (hAHint t).aestronglyMeasurable
      calc MeasureTheory.eLpNorm
            ((fun t' ω => (LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas
              h_sq_int_global n) t' ω) ^ 2
                - ∫ u in Set.Icc (0 : ℝ) t', ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas
                  h_sq_int_global n).eval u ω) ^ 2 ∂volume) t
              - fun ω => (F t ω) ^ 2 - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) 1 P
          = MeasureTheory.eLpNorm
              ((fun ω => (LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas
                h_sq_int_global n) t ω) ^ 2
                  - (F t ω) ^ 2)
                - fun ω => (∫ u in Set.Icc (0 : ℝ) t,
                    ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval u ω) ^ 2 ∂volume)
                  - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) 1 P := by
            refine MeasureTheory.eLpNorm_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
            simp only [Pi.sub_apply]; ring
        _ ≤ _ := MeasureTheory.eLpNorm_sub_le hXaesm hYaesm le_rfl
    · have hzero : ∀ n, MeasureTheory.eLpNorm
          ((fun t' ω => (LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas
            h_sq_int_global n) t' ω) ^ 2
              - ∫ u in Set.Icc (0 : ℝ) t', ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas
                h_sq_int_global n).eval u ω) ^ 2 ∂volume) t
            - fun ω => (F t ω) ^ 2 - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) 1 P = 0 := by
        intro n
        refine (MeasureTheory.eLpNorm_eq_zero_of_ae_zero ?_)
        filter_upwards [LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_zero_of_neg W ℱ hℱ H h_meas h_progMeas
          h_sq_int_global ht] with ω hF0
        simp only [Pi.sub_apply, Pi.zero_apply,
          LevyStochCalc.Brownian.Ito.simpleIntegral_eq_zero_of_nonpos W _ (le_of_lt ht) ω, hF, hF0,
          Set.Icc_eq_empty (not_le.mpr ht)]
        simp
      simp only [hzero]; exact tendsto_const_nhds
end MasterSequence

end LevyStochCalc.Brownian.Ito


