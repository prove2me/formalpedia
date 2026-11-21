-- Prove2me | Definitions.Def_SourceProof_580018e2ba31f91ba73e0981
-- name    : SourceProof_580018e2ba31f91ba73e0981
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:32:26.828478+00:00
-- url     : https://prove2.me/theorems/d3714ceb-6b47-4554-b127-3a1b36adfe9a
-- title:
--   LevyStochCalc source module: SourceProof_580018e2ba31f91ba73e0981
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.martingale_rightCont_quadVar_stochasticIntegralBrownian` comes from the `LevyStochCalc.Brownian.ItoL2CompletionApi` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionQuadVar_F001
import Definitions.Def_SourceProof_35156ff6984aa5b4b399bdef
import Definitions.Def_SourceProof_77343081f4784a6d686f59fe
import Definitions.Def_SourceProof_a4392a5b4c55fcf741a6a6c1

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: the `stochasticIntegral` API

The martingale property of the compensated square for the right-continuation `ℱ₊` of `ℱ`,
the unified existence theorem `itoIsometry_brownian_unified_existence` combining the
martingale, quadratic-variation and isometry conclusions, the isometry for differences of
integrands, and the `stochasticIntegral` interface with `itoIsometry`,
`quadVar_stochasticIntegral` and `martingale_stochasticIntegral`.
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

theorem _root_.Prove2MeSourceProof.h_580018e2ba31f91ba73e0981 :
    MeasureTheory.Martingale
      (fun t ω => (stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global t ω) ^ 2
        - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume)
      ℱ.rightCont P := by
  refine _root_.Prove2MeSourceProof.h_35156ff6984aa5b4b399bdef
    (_root_.Prove2MeSourceProof.h_a4392a5b4c55fcf741a6a6c1 W ℱ hℱ H h_meas h_progMeas h_sq_int_global)
    (fun s => ?_)
  set F := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global with hFdef
  -- `F²`-part: right-`L¹`-continuity of the square.
  have hF2 : Filter.Tendsto (fun r => MeasureTheory.eLpNorm
      (fun ω => (F r ω) ^ 2 - (F s ω) ^ 2) 1 P) (nhdsWithin s (Set.Ioi s)) (nhds 0) :=
    _root_.Prove2MeSourceProof.h_6be12e51c788a72f4de041a3 (l := nhdsWithin s (Set.Ioi s)) (a := fun r => F r) (b := F s)
      (fun r => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas
        h_sq_int_global r).1.aemeasurable)
      (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global s).1.aemeasurable
      (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global s).2.ne
      (_root_.Prove2MeSourceProof.h_77343081f4784a6d686f59fe W ℱ hℱ H h_meas h_progMeas
        h_sq_int_global s)
  -- compensator part: right-`L¹`-continuity of `A_t = ∫₀ᵗ H²`.
  have hA : Filter.Tendsto (fun r => MeasureTheory.eLpNorm
      (fun ω => (∫ u in Set.Icc (0 : ℝ) r, (H ω u) ^ 2 ∂volume)
        - ∫ u in Set.Icc (0 : ℝ) s, (H ω u) ^ 2 ∂volume) 1 P)
      (nhdsWithin s (Set.Ioi s)) (nhds 0) := by
    rcases le_or_gt 0 s with hs | hs
    · have hslab := _root_.Prove2MeSourceProof.h_7a12160ca4d56ce7d0871bc7 (fun ω u => (‖H ω u‖₊ : ℝ≥0∞) ^ 2)
        ((h_meas.nnnorm.coe_nnreal_ennreal).pow_const 2) hs (lt_add_one s)
        (h_sq_int_global (s + 1) (by linarith)).ne
      refine hslab.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r hr
      have hsr : s ≤ r := le_of_lt hr
      have hrpos : 0 < r := lt_of_le_of_lt hs hr
      have hHr : ∀ᵐ ω ∂P, MeasureTheory.Integrable
          (fun u => (H ω u) ^ 2) (volume.restrict (Set.Icc (0 : ℝ) r)) :=
        (_root_.Prove2MeSourceProof.h_560d23a90584c8e4562d928f H h_meas h_sq_int_global hrpos).integrable_sq.prod_right_ae
      rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
      refine (lintegral_congr_ae ?_).symm
      filter_upwards [hHr] with ω hHrω
      have hHsω : MeasureTheory.Integrable (fun u => (H ω u) ^ 2)
          (volume.restrict (Set.Icc (0 : ℝ) s)) :=
        hHrω.mono_measure (MeasureTheory.Measure.restrict_mono (Set.Icc_subset_Icc_right hsr)
          (le_refl _))
      have hHscω : MeasureTheory.Integrable (fun u => (H ω u) ^ 2)
          (volume.restrict (Set.Ioc s r)) :=
        hHrω.mono_measure (MeasureTheory.Measure.restrict_mono
          (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc_left hs)) (le_refl _))
      have hsplit : (∫ u in Set.Icc (0 : ℝ) r, (H ω u) ^ 2 ∂volume)
          - ∫ u in Set.Icc (0 : ℝ) s, (H ω u) ^ 2 ∂volume
          = ∫ u in Set.Ioc s r, (H ω u) ^ 2 ∂volume := by
        rw [← Set.Icc_union_Ioc_eq_Icc hs hsr,
          MeasureTheory.setIntegral_union
            (Set.disjoint_left.mpr (fun x hx1 hx2 => absurd hx2.1 (not_lt.mpr hx1.2)))
            measurableSet_Ioc hHsω hHscω]
        ring
      rw [hsplit, ← ofReal_norm, Real.norm_eq_abs,
        abs_of_nonneg (MeasureTheory.integral_nonneg (fun u => sq_nonneg _)),
        MeasureTheory.ofReal_integral_eq_lintegral_ofReal hHscω
          (Filter.Eventually.of_forall (fun u => sq_nonneg _))]
      refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioc (fun u _ => ?_)
      rw [show (‖H ω u‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal ((H ω u) ^ 2) from by
        rw [show (‖H ω u‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖H ω u‖ from (ofReal_norm _).symm,
          ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]]
    · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [Ioo_mem_nhdsGT hs] with r hr
      have hAr : (fun u => (H · u) ^ 2) = (fun u => (H · u) ^ 2) := rfl
      symm
      rw [show (fun ω => (∫ u in Set.Icc (0 : ℝ) r, (H ω u) ^ 2 ∂volume)
            - ∫ u in Set.Icc (0 : ℝ) s, (H ω u) ^ 2 ∂volume) = (0 : Ω → ℝ) from by
        funext ω
        rw [Set.Icc_eq_empty (not_le.mpr hr.2), Set.Icc_eq_empty (not_le.mpr hs)]
        simp]
      exact MeasureTheory.eLpNorm_zero
  -- combine the two parts.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by simpa using hF2.add hA)
    (Filter.Eventually.of_forall (fun r => bot_le)) (Filter.Eventually.of_forall (fun r => ?_))
  have hF2aesm : MeasureTheory.AEStronglyMeasurable (fun ω => (F r ω) ^ 2 - (F s ω) ^ 2) P :=
    (((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas
      h_sq_int_global r).1.aemeasurable.pow_const
        2).aestronglyMeasurable).sub
      (((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas
        h_sq_int_global s).1.aemeasurable.pow_const
        2).aestronglyMeasurable)
  have hAaesm : MeasureTheory.AEStronglyMeasurable
      (fun ω => (∫ u in Set.Icc (0 : ℝ) r, (H ω u) ^ 2 ∂volume)
        - ∫ u in Set.Icc (0 : ℝ) s, (H ω u) ^ 2 ∂volume) P :=
    ((LevyStochCalc.Brownian.Ito.compensatorH_adapted ℱ H h_progMeas r).mono
      (ℱ.le r)).aestronglyMeasurable.sub
      (((LevyStochCalc.Brownian.Ito.compensatorH_adapted ℱ H h_progMeas s).mono
        (ℱ.le s)).aestronglyMeasurable)
  calc MeasureTheory.eLpNorm
        ((fun t ω => (F t ω) ^ 2 - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) r
          - fun ω => (F s ω) ^ 2 - ∫ u in Set.Icc (0 : ℝ) s, (H ω u) ^ 2 ∂volume) 1 P
      = MeasureTheory.eLpNorm
          ((fun ω => (F r ω) ^ 2 - (F s ω) ^ 2)
            - fun ω => (∫ u in Set.Icc (0 : ℝ) r, (H ω u) ^ 2 ∂volume)
              - ∫ u in Set.Icc (0 : ℝ) s, (H ω u) ^ 2 ∂volume) 1 P := by
        refine MeasureTheory.eLpNorm_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
        simp only [Pi.sub_apply]; ring
    _ ≤ _ := MeasureTheory.eLpNorm_sub_le hF2aesm hAaesm le_rfl
end MasterSequence

end LevyStochCalc.Brownian.Ito


