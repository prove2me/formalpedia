-- Prove2me | Definitions.Def_SourceProof_f68e93dfb81b09358de9c4e9
-- name    : SourceProof_f68e93dfb81b09358de9c4e9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:09:20.817717+00:00
-- url     : https://prove2.me/theorems/51133597-f9ec-4e90-87ef-f3823b4fe7c4
-- title:
--   LevyStochCalc source module: SourceProof_f68e93dfb81b09358de9c4e9
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.masterApprox_eval_tendsto` comes from the `LevyStochCalc.Brownian.ItoL2CompletionMaster` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionMaster_F000

open private tendsto_master_tol from Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionMaster_F000
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


theorem _root_.Prove2MeSourceProof.h_f68e93dfb81b09358de9c4e9 {t : ℝ} :
    Filter.Tendsto (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖H ω s - (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P)
      Filter.atTop (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds tendsto_master_tol
    (Filter.Eventually.of_forall (fun n => bot_le)) ?_
  filter_upwards [Filter.eventually_ge_atTop ⌈t⌉₊] with n hn
  have htn : t ≤ (n : ℝ) + 1 := by
    have h1 : t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil t
    have h2 : (⌈t⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖H ω s - (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval s ω‖₊ : ℝ≥0∞) ^ 2
            ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) ((n : ℝ) + 1),
          (‖H ω s - (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval s ω‖₊ : ℝ≥0∞) ^ 2
            ∂volume ∂P :=
        MeasureTheory.lintegral_mono
          (fun ω => lintegral_mono_set (Set.Icc_subset_Icc_right htn))
    _ ≤ ((n : ℝ≥0∞) + 1)⁻¹ := le_of_lt (LevyStochCalc.Brownian.Ito.masterApprox_within ℱ H h_meas h_progMeas h_sq_int_global n)
end MasterSequence

end LevyStochCalc.Brownian.Ito


