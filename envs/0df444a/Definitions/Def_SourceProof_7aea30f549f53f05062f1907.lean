-- Prove2me | Definitions.Def_SourceProof_7aea30f549f53f05062f1907
-- name    : SourceProof_7aea30f549f53f05062f1907
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:26:08.788458+00:00
-- url     : https://prove2.me/theorems/48470f01-cd17-43a8-92db-c3065c29d233
-- title:
--   LevyStochCalc source module: SourceProof_7aea30f549f53f05062f1907
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.isometry_stochasticIntegralBrownian` comes from the `LevyStochCalc.Brownian.ItoL2CompletionQuadVar` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionMaster_F003
import Definitions.Def_SourceProof_1783d6024dc5fa5c520e82bb

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

theorem _root_.Prove2MeSourceProof.h_7aea30f549f53f05062f1907 {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas
      h_sq_int_global T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  set Flp := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownianLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global T with hFlp
  have htend : Filter.Tendsto (fun n => LevyStochCalc.Brownian.Ito.masterLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global T n)
      Filter.atTop (nhds Flp) :=
    (_root_.Prove2MeSourceProof.h_7edd2e3de7413bb1cc6dc69c W ℱ hℱ H h_meas h_progMeas h_sq_int_global (le_of_lt hT)).tendsto_limUnder
  have hn := (htend.enorm).ennrpow_const 2
  simp only [MeasureTheory.Lp.enorm_def] at hn
  -- limit `eLpNorm ↑↑Flp ^ 2 = ∫⁻‖F T‖²`
  have hlim : MeasureTheory.eLpNorm (↑↑Flp : Ω → ℝ) 2 P ^ (2 : ℝ)
      = ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas
        h_sq_int_global T ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    rw [LevyStochCalc.Brownian.Ito.eLpNorm_sq_eq_lintegral_nnnorm_sq]
    refine lintegral_congr_ae ?_
    filter_upwards [LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_eq W ℱ hℱ H h_meas h_progMeas h_sq_int_global T]
      with ω hF
    rw [hF]
  rw [hlim] at hn
  have h_a : Filter.Tendsto (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop
      (nhds (∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global T ω‖₊
        : ℝ≥0∞) ^ 2 ∂P)) := by
    refine hn.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop ⌈T⌉₊] with n hn'
    have hcn : T ≤ (n : ℝ) + 1 := by
      have h1' : T ≤ (⌈T⌉₊ : ℝ) := Nat.le_ceil T
      have h2' : (⌈T⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn'
      linarith
    rw [MeasureTheory.eLpNorm_congr_ae
        (LevyStochCalc.Brownian.Ito.masterLp_coeFn W ℱ hℱ H h_meas h_progMeas h_sq_int_global n (le_of_lt hT) hcn),
      LevyStochCalc.Brownian.Ito.eLpNorm_sq_eq_lintegral_nnnorm_sq,
      _root_.Prove2MeSourceProof.h_07211334eb93145a1521a908 W ℱ hℱ
        (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n)
        (LevyStochCalc.Brownian.Ito.masterApprox_adapt ℱ H h_meas h_progMeas h_sq_int_global n) (le_of_lt hT)]
  exact tendsto_nhds_unique h_a
    (_root_.Prove2MeSourceProof.h_1783d6024dc5fa5c520e82bb ℱ H h_meas h_progMeas h_sq_int_global hT)
end MasterSequence

end LevyStochCalc.Brownian.Ito


