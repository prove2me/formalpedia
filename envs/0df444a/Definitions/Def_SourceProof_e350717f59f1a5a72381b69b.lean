-- Prove2me | Definitions.Def_SourceProof_e350717f59f1a5a72381b69b
-- name    : SourceProof_e350717f59f1a5a72381b69b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:26:03.243745+00:00
-- url     : https://prove2.me/theorems/a890751d-bd8e-4157-b2fd-51d830d1d12d
-- title:
--   LevyStochCalc source module: SourceProof_e350717f59f1a5a72381b69b
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.integrable_abs_itoIncrement_pow_three` comes from the `LevyStochCalc.Brownian.ItoProcess` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoProcess_F000
import Definitions.Def_SourceProof_4ef3e5b73189336215f644cf

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô processes and the moments of their increments

An Itô process is `X_t = X₀ + ∫_{[0,t]} b_s ds + ∫_0^t H_s dW_s` for a bounded drift `b` and an
`L²` integrand `H`. Its increment across a window is the drift's window integral plus the Itô
integral's increment, so its moments follow from the drift bound and the increment moments of
the Itô integral.

## Main statements

* `LevyStochCalc.Brownian.Ito.itoProcess` — the process itself.
* `LevyStochCalc.Brownian.Ito.itoProcess_sub` — the increment splits into drift and martingale
  parts.
* `LevyStochCalc.Brownian.Ito.integral_sq_itoProcess_sub_le` — `𝔼|ΔX|² ≤ 2B²(Δt)² + 2C²Δt`.
* `LevyStochCalc.Brownian.Ito.integral_abs_sub_stochasticIntegral_le` — `𝔼|ΔM| ≤ C√(Δt)`.
* `LevyStochCalc.Brownian.Ito.integral_abs_itoProcess_sub_le` — `𝔼|ΔX| ≤ BΔt + C√(Δt)`.
* `LevyStochCalc.Brownian.Ito.integrable_abs_itoIncrement_pow_three` — the cube of the absolute
  increment is integrable.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Drift

variable {P : Measure Ω} [IsProbabilityMeasure P]

end Drift

section Process

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

variable {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hℱ hC0 hCH in

theorem _root_.Prove2MeSourceProof.h_e350717f59f1a5a72381b69b
    (bdrift : Ω → ℝ → ℝ) (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
    MeasureTheory.Integrable (fun ω : Ω =>
      |(∫ s in Set.Ioc u v, bdrift ω s ∂volume)
        + (stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω)| ^ 3) P := by
  have hDint := LevyStochCalc.Brownian.Ito.integrable_abs_drift_pow_three (P := P) bdrift hbm hB0 hB huv.le
  have hDmeas : Measurable fun ω : Ω => ∫ s in Set.Ioc u v, bdrift ω s ∂volume :=
    LevyStochCalc.measurable_setIntegral_Ioc hbm _ _
  have hMint := (_root_.Prove2MeSourceProof.h_4ef3e5b73189336215f644cf W ℱ hℱ H hm hp hq hC0 hCH hu huv).1
  have hMmeas := LevyStochCalc.Brownian.Ito.measurable_sub_stochasticIntegralBrownian W ℱ hℱ H hm hp hq u v
  refine ((hDint.add hMint).const_mul 4).mono
    (((hDmeas.add hMmeas).abs.pow_const 3).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) 3)]
  refine le_trans ?_ (le_abs_self _)
  have h3 : |(∫ s in Set.Ioc u v, bdrift ω s ∂volume)
      + (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω)| ^ 3
      ≤ (|∫ s in Set.Ioc u v, bdrift ω s ∂volume|
        + |LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω|) ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg _) (abs_add_le _ _) 3
  exact h3.trans (LevyStochCalc.Brownian.Ito.add_pow_three_le_four (abs_nonneg _) (abs_nonneg _))
end Process

end LevyStochCalc.Brownian.Ito


