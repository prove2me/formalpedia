-- Prove2me | Definitions.Def_SourceProof_2554b195ead815ae5442020c
-- name    : SourceProof_2554b195ead815ae5442020c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:14:35.212987+00:00
-- url     : https://prove2.me/theorems/cfd1360f-f4de-4ca2-a876-f8600e51e048
-- title:
--   LevyStochCalc source module: SourceProof_2554b195ead815ae5442020c
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.masterApprox_tendsto_L2` comes from the `LevyStochCalc.Brownian.ItoL2CompletionMaster` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionMaster_F002

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

theorem _root_.Prove2MeSourceProof.h_2554b195ead815ae5442020c {t : ℝ} (ht_nn : 0 ≤ t) :
    Filter.Tendsto (fun n => MeasureTheory.eLpNorm
        (fun ω => simpleIntegral W (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n) t ω
          - stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global t ω) 2 P)
      Filter.atTop (nhds 0) := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  set Flp := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownianLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t with hFlp
  have h1 : Filter.Tendsto (fun n => LevyStochCalc.Brownian.Ito.masterLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t n)
      Filter.atTop (nhds Flp) :=
    (_root_.Prove2MeSourceProof.h_7edd2e3de7413bb1cc6dc69c W ℱ hℱ H h_meas h_progMeas h_sq_int_global ht_nn).tendsto_limUnder
  have hmem : MeasureTheory.MemLp (↑↑Flp : Ω → ℝ) 2 P := MeasureTheory.Lp.memLp Flp
  rw [← MeasureTheory.Lp.toLp_coeFn Flp hmem] at h1
  have h2 := (MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm
    (fun n => LevyStochCalc.Brownian.Ito.masterLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t n) (↑↑Flp) hmem).mp h1
  refine h2.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop ⌈t⌉₊] with n hn
  have hcn : t ≤ (n : ℝ) + 1 := by
    have h1' : t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil t
    have h2' : (⌈t⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  refine MeasureTheory.eLpNorm_congr_ae ?_
  filter_upwards [LevyStochCalc.Brownian.Ito.masterLp_coeFn W ℱ hℱ H h_meas h_progMeas h_sq_int_global n ht_nn hcn,
    LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_eq W ℱ hℱ H h_meas h_progMeas h_sq_int_global t] with ω hω hF
  simp only [Pi.sub_apply]
  rw [hω, hF]
end MasterSequence

end LevyStochCalc.Brownian.Ito


