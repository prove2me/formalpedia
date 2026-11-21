-- Prove2me | Definitions.Def_SourceProof_2631a3786acbcf68272d1d52
-- name    : SourceProof_2631a3786acbcf68272d1d52
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:28:41.764011+00:00
-- url     : https://prove2.me/theorems/024dd271-e89b-4165-95f7-cea4509f1cbc
-- title:
--   LevyStochCalc source module: SourceProof_2631a3786acbcf68272d1d52
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_zero` comes from the `LevyStochCalc.Brownian.ItoZero` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_39285c9e8cb91346b858af97
import Definitions.Def_SourceProof_7aea30f549f53f05062f1907

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Itô integral of the zero integrand

The `L²`-isometry forces the Itô integral of the zero integrand to vanish almost surely, at
every time. This is what lets a coordinate of a vector Itô process carry no diffusion.

## Main statements

* `LevyStochCalc.Probability.progressivelyMeasurable_const` — a constant process is
  progressively measurable.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_zero` — the Itô integral of the zero
  integrand vanishes almost surely.
-/

namespace LevyStochCalc

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace Brownian.Ito

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in

theorem _root_.Prove2MeSourceProof.h_2631a3786acbcf68272d1d52
    (hm : Measurable (Function.uncurry fun (_ : Ω) (_ : ℝ) => (0 : ℝ)))
    (hp : Probability.ProgressivelyMeasurable ℱ fun (_ : Ω) (_ : ℝ) => (0 : ℝ))
    (hq : ∀ T, 0 < T → ∫⁻ _ω, ∫⁻ _s in Set.Icc (0 : ℝ) T,
      (‖(0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) (t : ℝ) :
    stochasticIntegralBrownian W ℱ hℱ (fun _ _ => (0 : ℝ)) hm hp hq t =ᵐ[P] 0 := by
  rcases le_or_gt t 0 with ht | ht
  · exact _root_.Prove2MeSourceProof.h_39285c9e8cb91346b858af97 W ℱ hℱ _ hm hp hq ht
  · have hiso := _root_.Prove2MeSourceProof.h_7aea30f549f53f05062f1907 W ℱ hℱ (fun _ _ => (0 : ℝ)) hm hp hq ht
    have hrhs : ∫⁻ ω, ∫⁻ _s in Set.Icc (0 : ℝ) t,
        (‖(0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P = 0 := by
      simp
    rw [hrhs] at hiso
    have hmeas : AEMeasurable (fun ω => (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
        (fun _ _ => (0 : ℝ)) hm hp hq t ω‖₊ : ℝ≥0∞) ^ 2) P :=
      ((((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ _ hm hp hq t).mono
        (ℱ.le t)).measurable.nnnorm.coe_nnreal_ennreal).pow_const 2).aemeasurable
    have hzero := (MeasureTheory.lintegral_eq_zero_iff' hmeas).mp hiso
    filter_upwards [hzero] with ω hω
    have : (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun _ _ => (0 : ℝ)) hm hp hq t ω‖₊ : ℝ≥0∞) = 0 := by
      simpa [pow_eq_zero_iff] using hω
    simpa using this
end Brownian.Ito

end LevyStochCalc


