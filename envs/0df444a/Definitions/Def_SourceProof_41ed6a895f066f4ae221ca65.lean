-- Prove2me | Definitions.Def_SourceProof_41ed6a895f066f4ae221ca65
-- name    : SourceProof_41ed6a895f066f4ae221ca65
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:09:26.168409+00:00
-- url     : https://prove2.me/theorems/4cc1cfc1-a5a4-47c6-9807-31d17e309581
-- title:
--   LevyStochCalc source module: SourceProof_41ed6a895f066f4ae221ca65
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.masterApprox_cauchy_le` comes from the `LevyStochCalc.Brownian.ItoL2CompletionMaster` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionMaster_F000
import Definitions.Def_SourceProof_e4a003adac246e81fe5cee0f

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

theorem _root_.Prove2MeSourceProof.h_41ed6a895f066f4ae221ca65 (n m : ℕ) {t : ℝ} (ht_nn : 0 ≤ t) :
    ∫⁻ ω, (‖simpleIntegral W (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n) t ω
        - simpleIntegral W (masterApprox ℱ H h_meas h_progMeas h_sq_int_global m) t ω‖₊
          : ℝ≥0∞) ^ 2 ∂P
      ≤ 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
            (‖H ω s - (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval s ω‖₊ : ℝ≥0∞) ^ 2
              ∂volume ∂P)
          + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
            (‖H ω s - (masterApprox ℱ H h_meas h_progMeas h_sq_int_global m).eval s ω‖₊ : ℝ≥0∞) ^ 2
              ∂volume ∂P) := by
  set Gn := LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n with hGn
  set Gm := LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global m with hGm
  rw [LevyStochCalc.Brownian.Ito.masterApprox_diff_isometry W ℱ hℱ H h_meas h_progMeas h_sq_int_global n m ht_nn]
  -- abbreviations for the two error densities
  set A : Ω → ℝ → ℝ≥0∞ := fun ω s => (‖H ω s - Gn.eval s ω‖₊ : ℝ≥0∞) ^ 2 with hA
  set B : Ω → ℝ → ℝ≥0∞ := fun ω s => (‖H ω s - Gm.eval s ω‖₊ : ℝ≥0∞) ^ 2 with hB
  have h_point : ∀ ω, ∀ s,
      (‖Gn.eval s ω - Gm.eval s ω‖₊ : ℝ≥0∞) ^ 2 ≤ 2 * (A ω s + B ω s) := by
    intro ω s
    have hrw : Gn.eval s ω - Gm.eval s ω
        = -(H ω s - Gn.eval s ω) + (H ω s - Gm.eval s ω) := by ring
    rw [hrw, hA, hB]
    refine le_trans (_root_.Prove2MeSourceProof.h_e4a003adac246e81fe5cee0f _ _) ?_
    rw [show ‖-(H ω s - Gn.eval s ω)‖₊ = ‖H ω s - Gn.eval s ω‖₊ from by rw [nnnorm_neg]]
  -- joint measurability of `A` and the `s`-section measurability
  have hH_pair : Measurable (fun p : Ω × ℝ => H p.1 p.2) := h_meas
  have hA_pair : Measurable (fun p : Ω × ℝ => A p.1 p.2) := by
    rw [hA]
    exact (((hH_pair.sub Gn.eval_jointly_measurable).nnnorm).coe_nnreal_ennreal).pow_const 2
  have hB_pair : Measurable (fun p : Ω × ℝ => B p.1 p.2) := by
    rw [hB]
    exact (((hH_pair.sub Gm.eval_jointly_measurable).nnnorm).coe_nnreal_ennreal).pow_const 2
  have hA_s : ∀ ω, Measurable (A ω) := fun ω =>
    hA_pair.comp (measurable_const.prodMk measurable_id)
  have hA_outer : Measurable (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t, A ω s ∂volume) :=
    Measurable.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) t)) hA_pair
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖Gn.eval s ω - Gm.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, 2 * (A ω s + B ω s) ∂volume ∂P :=
        MeasureTheory.lintegral_mono (fun ω =>
          MeasureTheory.lintegral_mono (fun s => h_point ω s))
    _ = 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, A ω s ∂volume ∂P)
          + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, B ω s ∂volume ∂P) := by
        have h_inner : ∀ ω, (∫⁻ s in Set.Icc (0 : ℝ) t, 2 * (A ω s + B ω s) ∂volume)
            = 2 * ((∫⁻ s in Set.Icc (0 : ℝ) t, A ω s ∂volume)
              + ∫⁻ s in Set.Icc (0 : ℝ) t, B ω s ∂volume) := by
          intro ω
          rw [MeasureTheory.lintegral_const_mul' 2 _ (by norm_num),
              MeasureTheory.lintegral_add_left' (hA_s ω).aemeasurable]
        rw [MeasureTheory.lintegral_congr h_inner,
            MeasureTheory.lintegral_const_mul' 2 _ (by norm_num),
            MeasureTheory.lintegral_add_left' hA_outer.aemeasurable]
end MasterSequence

end LevyStochCalc.Brownian.Ito


