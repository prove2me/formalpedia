-- Prove2me | Definitions.Def_SourceProof_44f5bfd0fb515ee218ff3537
-- name    : SourceProof_44f5bfd0fb515ee218ff3537
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:21:52.174251+00:00
-- url     : https://prove2.me/theorems/58cf9c9e-46c3-4f05-9199-8aadbae79090
-- title:
--   LevyStochCalc source module: SourceProof_44f5bfd0fb515ee218ff3537
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.integral_abs_sub_stochasticIntegral_le` comes from the `LevyStochCalc.Brownian.ItoProcess` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_DriftIncrement_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoIncrementMomentBounds_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoIncrementMomentBounds_F002
import Definitions.Def_LevyStochCalc_Probability_AbsMoment_F000
import Definitions.Def_SourceProof_33cc866be12cedca71971a8f
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

theorem _root_.Prove2MeSourceProof.h_44f5bfd0fb515ee218ff3537 {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
    MeasureTheory.Integrable (fun ω : Ω =>
        |stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω|) P
      ∧ ∫ ω, |stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω| ∂P
          ≤ C * Real.sqrt (v - u) := by
  obtain ⟨hMsq, hMle⟩ := _root_.Prove2MeSourceProof.h_9a9fab4277e23ec64788cbe8 W ℱ hℱ H hm hp hq hC0 hCH hu huv
  have hMmeas := LevyStochCalc.Brownian.Ito.measurable_sub_stochasticIntegralBrownian W ℱ hℱ H hm hp hq u v
  have hyoung : ∀ x : ℝ, |x| ≤ (x ^ 2 + 1) / 2 := by
    intro x
    nlinarith [sq_nonneg (|x| - 1), sq_abs x]
  have hMabs : MeasureTheory.Integrable (fun ω : Ω =>
      |LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω|) P := by
    refine ((hMsq.add (MeasureTheory.integrable_const 1)).div_const 2).mono
      hMmeas.abs.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
    exact (hyoung _).trans (le_abs_self _)
  refine ⟨hMabs, ?_⟩
  have hsqrt : Real.sqrt (C ^ 2 * (v - u)) = C * Real.sqrt (v - u) := by
    rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC0]
  rw [← hsqrt]
  exact _root_.Prove2MeSourceProof.h_33cc866be12cedca71971a8f hMabs hMsq hMle
end Process

end LevyStochCalc.Brownian.Ito


