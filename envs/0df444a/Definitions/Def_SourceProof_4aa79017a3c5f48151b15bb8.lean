-- Prove2me | Definitions.Def_SourceProof_4aa79017a3c5f48151b15bb8
-- name    : SourceProof_4aa79017a3c5f48151b15bb8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:24:46.433336+00:00
-- url     : https://prove2.me/theorems/f49db147-6a8d-4a75-8f3c-b1237b18a5cc
-- title:
--   LevyStochCalc source module: SourceProof_4aa79017a3c5f48151b15bb8
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.integral_abs_itoProcess_sub_le` comes from the `LevyStochCalc.Brownian.ItoProcess` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoProcess_F000
import Definitions.Def_SourceProof_44f5bfd0fb515ee218ff3537

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

theorem _root_.Prove2MeSourceProof.h_4aa79017a3c5f48151b15bb8
    (X₀ : Ω → ℝ) (bdrift : Ω → ℝ → ℝ) (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
    MeasureTheory.Integrable (fun ω : Ω =>
        |itoProcess W ℱ hℱ H hm hp hq X₀ bdrift v ω
          - itoProcess W ℱ hℱ H hm hp hq X₀ bdrift u ω|) P
      ∧ ∫ ω, |itoProcess W ℱ hℱ H hm hp hq X₀ bdrift v ω
            - itoProcess W ℱ hℱ H hm hp hq X₀ bdrift u ω| ∂P
          ≤ B * (v - u) + C * Real.sqrt (v - u) := by
  have key : ∀ ω : Ω, LevyStochCalc.Brownian.Ito.itoProcess W ℱ hℱ H hm hp hq X₀ bdrift v ω
      - LevyStochCalc.Brownian.Ito.itoProcess W ℱ hℱ H hm hp hq X₀ bdrift u ω
      = (∫ s in Set.Ioc u v, bdrift ω s ∂volume)
        + (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω) := fun ω =>
    LevyStochCalc.Brownian.Ito.itoProcess_sub W ℱ hℱ H hm hp hq X₀ bdrift hbm hB hu huv.le ω
  simp_rw [key]
  obtain ⟨hMabs, hMabsle⟩ :=
    _root_.Prove2MeSourceProof.h_44f5bfd0fb515ee218ff3537 W ℱ hℱ H hm hp hq hC0 hCH hu huv
  have hMmeas := LevyStochCalc.Brownian.Ito.measurable_sub_stochasticIntegralBrownian W ℱ hℱ H hm hp hq u v
  have hDmeas : Measurable fun ω : Ω => ∫ s in Set.Ioc u v, bdrift ω s ∂volume :=
    LevyStochCalc.measurable_setIntegral_Ioc hbm _ _
  have hDabs := LevyStochCalc.Brownian.Ito.integrable_abs_drift (P := P) bdrift hbm hB0 hB huv.le
  have hDle := LevyStochCalc.Brownian.Ito.integral_abs_drift_le (P := P) bdrift hbm hB0 hB huv.le
  have hpt : ∀ ω : Ω, |(∫ s in Set.Ioc u v, bdrift ω s ∂volume)
        + (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω)|
      ≤ |∫ s in Set.Ioc u v, bdrift ω s ∂volume|
        + |LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω| := fun ω => abs_add_le _ _
  have hXabs : MeasureTheory.Integrable (fun ω : Ω =>
      |(∫ s in Set.Ioc u v, bdrift ω s ∂volume)
        + (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω)|) P := by
    refine (hDabs.add hMabs).mono ((hDmeas.add hMmeas).abs.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
    exact (hpt ω).trans (le_abs_self _)
  refine ⟨hXabs, ?_⟩
  calc ∫ ω, |(∫ s in Set.Ioc u v, bdrift ω s ∂volume)
        + (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω)| ∂P
      ≤ ∫ ω, (|∫ s in Set.Ioc u v, bdrift ω s ∂volume|
          + |LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω|) ∂P :=
        MeasureTheory.integral_mono hXabs (hDabs.add hMabs) hpt
    _ = (∫ ω, |∫ s in Set.Ioc u v, bdrift ω s ∂volume| ∂P)
        + ∫ ω, |LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω| ∂P :=
        MeasureTheory.integral_add hDabs hMabs
    _ ≤ B * (v - u) + C * Real.sqrt (v - u) := add_le_add hDle hMabsle
end Process

end LevyStochCalc.Brownian.Ito


