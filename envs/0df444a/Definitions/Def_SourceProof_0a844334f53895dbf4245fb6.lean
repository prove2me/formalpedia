-- Prove2me | Definitions.Def_SourceProof_0a844334f53895dbf4245fb6
-- name    : SourceProof_0a844334f53895dbf4245fb6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:43:47.802177+00:00
-- url     : https://prove2.me/theorems/efa93b7e-2c59-49a9-9e87-b2332e4338fe
-- title:
--   LevyStochCalc source module: SourceProof_0a844334f53895dbf4245fb6
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_add` comes from the `LevyStochCalc.Brownian.ItoLinear` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoLinear_F001
import Definitions.Def_SourceProof_679fbec7203cd0a8616c5964
import Definitions.Def_SourceProof_700488d66fa58fc241f21293
import Definitions.Def_SourceProof_7aea30f549f53f05062f1907
import Definitions.Def_SourceProof_9ab1096355abba8f677466b8

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Additivity of the L² Itô integral in the integrand

The Itô isometry and the isometry of differences determine every squared `L²`-distance among
`∫ H₁ dW`, `∫ H₂ dW` and `∫ (H₁ + H₂) dW` in terms of the energies of `H₁`, `H₂`, `H₁ + H₂` and
`H₁ − H₂`. The parallelogram law for those energies then forces
`∫ (H₁ + H₂) dW = ∫ H₁ dW + ∫ H₂ dW` almost everywhere.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Energy

variable {H₁ H₂ : Ω → ℝ → ℝ}

end Energy

section Parallelogram

end Parallelogram

section Additivity

variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in

theorem _root_.Prove2MeSourceProof.h_0a844334f53895dbf4245fb6 {H₁ H₂ : Ω → ℝ → ℝ}
    (hm₁ : Measurable (Function.uncurry H₁)) (hm₂ : Measurable (Function.uncurry H₂))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ H₁)
    (hp₂ : Probability.ProgressivelyMeasurable ℱ H₂)
    (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hma : Measurable (Function.uncurry fun ω s => H₁ ω s + H₂ ω s))
    (hpa : Probability.ProgressivelyMeasurable ℱ fun ω s => H₁ ω s + H₂ ω s)
    (hqa : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s + H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    stochasticIntegralBrownian W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa T
      =ᵐ[P] fun ω => stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ T ω
        + stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ T ω := by
  have hqd : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    _root_.Prove2MeSourceProof.h_700488d66fa58fc241f21293 (fun ω s => LevyStochCalc.Brownian.Ito.sq_nnnorm_sub_le_two_mul _ _) hm₁ hm₂ hq₁ hq₂
  refine _root_.Prove2MeSourceProof.h_679fbec7203cd0a8616c5964
    (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H₁ hm₁ hp₁ hq₁ T)
    (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H₂ hm₂ hp₂ hq₂ T)
    (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa T)
    (hq₁ T hT).ne (hq₂ T hT).ne (hqa T hT).ne (hqd T hT).ne
    (_root_.Prove2MeSourceProof.h_7aea30f549f53f05062f1907 W ℱ hℱ H₁ hm₁ hp₁ hq₁ hT)
    (_root_.Prove2MeSourceProof.h_7aea30f549f53f05062f1907 W ℱ hℱ H₂ hm₂ hp₂ hq₂ hT)
    (_root_.Prove2MeSourceProof.h_7aea30f549f53f05062f1907 W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa hT)
    ?_ ?_
    (_root_.Prove2MeSourceProof.h_9ab1096355abba8f677466b8 W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ hT)
    (LevyStochCalc.Brownian.Ito.lintegral_energy_parallelogram (P := P) hm₁ hm₂ T)
  · refine Eq.trans (_root_.Prove2MeSourceProof.h_9ab1096355abba8f677466b8 W ℱ hℱ
      (fun ω s => H₁ ω s + H₂ ω s) H₁ hma hm₁ hpa hp₁ hqa hq₁ hT) ?_
    exact lintegral_congr fun ω => lintegral_congr fun s => by ring_nf
  · refine Eq.trans (_root_.Prove2MeSourceProof.h_9ab1096355abba8f677466b8 W ℱ hℱ
      (fun ω s => H₁ ω s + H₂ ω s) H₂ hma hm₂ hpa hp₂ hqa hq₂ hT) ?_
    exact lintegral_congr fun ω => lintegral_congr fun s => by ring_nf
end Additivity

section Scaling

variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

end Scaling

end LevyStochCalc.Brownian.Ito


