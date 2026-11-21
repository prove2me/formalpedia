-- Prove2me | Definitions.Def_SourceProof_00809733168215a41b1415ee
-- name    : SourceProof_00809733168215a41b1415ee
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:21:56.178243+00:00
-- url     : https://prove2.me/theorems/db4e89fc-e61b-4ca9-99e0-4a4328804f65
-- title:
--   LevyStochCalc source module: SourceProof_00809733168215a41b1415ee
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.integral_sq_itoProcess_sub_le` comes from the `LevyStochCalc.Brownian.ItoProcess` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoProcess_F000
import Definitions.Def_SourceProof_9a9fab4277e23ec64788cbe8

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

theorem _root_.Prove2MeSourceProof.h_00809733168215a41b1415ee
    (X₀ : Ω → ℝ) (bdrift : Ω → ℝ → ℝ) (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
    MeasureTheory.Integrable (fun ω : Ω =>
        (itoProcess W ℱ hℱ H hm hp hq X₀ bdrift v ω
          - itoProcess W ℱ hℱ H hm hp hq X₀ bdrift u ω) ^ 2) P
      ∧ ∫ ω, (itoProcess W ℱ hℱ H hm hp hq X₀ bdrift v ω
            - itoProcess W ℱ hℱ H hm hp hq X₀ bdrift u ω) ^ 2 ∂P
          ≤ 2 * (B * (v - u)) ^ 2 + 2 * (C ^ 2 * (v - u)) := by
  have key : ∀ ω : Ω, LevyStochCalc.Brownian.Ito.itoProcess W ℱ hℱ H hm hp hq X₀ bdrift v ω
      - LevyStochCalc.Brownian.Ito.itoProcess W ℱ hℱ H hm hp hq X₀ bdrift u ω
      = (∫ s in Set.Ioc u v, bdrift ω s ∂volume)
        + (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω) := fun ω =>
    LevyStochCalc.Brownian.Ito.itoProcess_sub W ℱ hℱ H hm hp hq X₀ bdrift hbm hB hu huv.le ω
  simp_rw [key]
  obtain ⟨hMint, hMle⟩ := _root_.Prove2MeSourceProof.h_9a9fab4277e23ec64788cbe8 W ℱ hℱ H hm hp hq hC0 hCH hu huv
  have hDint := LevyStochCalc.Brownian.Ito.integrable_drift_sq (P := P) bdrift hbm hB0 hB huv.le
  have hDle := LevyStochCalc.Brownian.Ito.integral_drift_sq_le (P := P) bdrift hbm hB0 hB huv.le
  have hDmeas : Measurable fun ω : Ω => ∫ s in Set.Ioc u v, bdrift ω s ∂volume :=
    LevyStochCalc.measurable_setIntegral_Ioc hbm _ _
  have hMmeas := LevyStochCalc.Brownian.Ito.measurable_sub_stochasticIntegralBrownian W ℱ hℱ H hm hp hq u v
  have hdom : MeasureTheory.Integrable (fun ω : Ω =>
      2 * (∫ s in Set.Ioc u v, bdrift ω s ∂volume) ^ 2
        + 2 * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω) ^ 2) P :=
    (hDint.const_mul 2).add (hMint.const_mul 2)
  have hpt : ∀ ω : Ω, ((∫ s in Set.Ioc u v, bdrift ω s ∂volume)
        + (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω)) ^ 2
      ≤ 2 * (∫ s in Set.Ioc u v, bdrift ω s ∂volume) ^ 2
        + 2 * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω) ^ 2 := by
    intro ω
    nlinarith [sq_nonneg ((∫ s in Set.Ioc u v, bdrift ω s ∂volume)
      - (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω))]
  have hXint : MeasureTheory.Integrable (fun ω : Ω =>
      ((∫ s in Set.Ioc u v, bdrift ω s ∂volume)
        + (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω)) ^ 2) P := by
    refine hdom.mono (((hDmeas.add hMmeas).pow_const 2).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (hpt ω).trans (le_abs_self _)
  refine ⟨hXint, ?_⟩
  calc ∫ ω, ((∫ s in Set.Ioc u v, bdrift ω s ∂volume)
        + (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω)) ^ 2 ∂P
      ≤ ∫ ω, (2 * (∫ s in Set.Ioc u v, bdrift ω s ∂volume) ^ 2
          + 2 * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω) ^ 2) ∂P :=
        MeasureTheory.integral_mono hXint hdom hpt
    _ = 2 * (∫ ω, (∫ s in Set.Ioc u v, bdrift ω s ∂volume) ^ 2 ∂P)
        + 2 * ∫ ω, (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω) ^ 2 ∂P := by
        rw [MeasureTheory.integral_add (hDint.const_mul 2) (hMint.const_mul 2),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    _ ≤ 2 * (B * (v - u)) ^ 2 + 2 * (C ^ 2 * (v - u)) := by
        have h1 : 2 * (∫ ω, (∫ s in Set.Ioc u v, bdrift ω s ∂volume) ^ 2 ∂P)
            ≤ 2 * (B * (v - u)) ^ 2 := by linarith
        have h2 : 2 * ∫ ω, (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
              - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω) ^ 2 ∂P
            ≤ 2 * (C ^ 2 * (v - u)) := by linarith
        linarith
end Process

end LevyStochCalc.Brownian.Ito


