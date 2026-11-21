-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionMaster_F003
-- name    : LevyStochCalc_Brownian_ItoL2CompletionMaster_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:14:59.358219+00:00
-- url     : https://prove2.me/theorems/004071eb-a241-4390-beeb-eac322bbcc79
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoL2CompletionMaster
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoL2CompletionMaster. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
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
/-- For `t < 0` the integral process is the zero `Lp` element. -/
lemma stochasticIntegralBrownianLp_eq_zero_of_neg {t : ℝ} (ht : t < 0) :
    stochasticIntegralBrownianLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t = 0 := by
  rw [stochasticIntegralBrownianLp]
  have heq : (fun n => masterLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t n)
      = fun _ => (0 : MeasureTheory.Lp ℝ 2 P) := by
    funext n; rw [masterLp, dif_neg (fun h => absurd h.1 (not_le.mpr ht))]
  rw [heq]
  exact tendsto_const_nhds.limUnder_eq
include hℱ in
/-- For `t < 0` the integral process is a.e. zero. -/
lemma stochasticIntegralBrownian_ae_zero_of_neg {t : ℝ} (ht : t < 0) :
    stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global t =ᵐ[P] 0 := by
  refine (stochasticIntegralBrownian_ae_eq W ℱ hℱ H h_meas h_progMeas h_sq_int_global t).trans ?_
  rw [stochasticIntegralBrownianLp_eq_zero_of_neg W ℱ hℱ H h_meas h_progMeas h_sq_int_global ht]
  exact MeasureTheory.Lp.coeFn_zero ℝ 2 P
end MasterSequence

end LevyStochCalc.Brownian.Ito


