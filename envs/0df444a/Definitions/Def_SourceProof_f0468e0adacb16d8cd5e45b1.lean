-- Prove2me | Definitions.Def_SourceProof_f0468e0adacb16d8cd5e45b1
-- name    : SourceProof_f0468e0adacb16d8cd5e45b1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:43:39.718646+00:00
-- url     : https://prove2.me/theorems/afcf5d36-1741-45ec-bdf7-9288a15f79a9
-- title:
--   LevyStochCalc source module: SourceProof_f0468e0adacb16d8cd5e45b1
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_const_mul` comes from the `LevyStochCalc.Brownian.ItoLinear` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_7aea30f549f53f05062f1907
import Definitions.Def_SourceProof_8b64fc95ec4c1a34f817a2e0
import Definitions.Def_SourceProof_9ab1096355abba8f677466b8
import Definitions.Def_SourceProof_b2a8a79da4bd7b154436ee26

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

end Additivity

section Scaling

variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in

theorem _root_.Prove2MeSourceProof.h_f0468e0adacb16d8cd5e45b1 {H : Ω → ℝ → ℝ}
    (hm : Measurable (Function.uncurry H)) (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (c : ℝ)
    (hmc : Measurable (Function.uncurry fun ω s => c * H ω s))
    (hpc : Probability.ProgressivelyMeasurable ℱ fun ω s => c * H ω s)
    (hqc : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖c * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    stochasticIntegralBrownian W ℱ hℱ (fun ω s => c * H ω s) hmc hpc hqc T
      =ᵐ[P] fun ω => c * stochasticIntegralBrownian W ℱ hℱ H hm hp hq T ω := by
  have hscale := _root_.Prove2MeSourceProof.h_8b64fc95ec4c1a34f817a2e0 (P := P) hm c T
  have hdiff : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖c * H ω s - H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      = ENNReal.ofReal ((c - 1) ^ 2)
        * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
    refine Eq.trans ?_ (_root_.Prove2MeSourceProof.h_8b64fc95ec4c1a34f817a2e0 (P := P) hm (c - 1) T)
    exact lintegral_congr fun ω => lintegral_congr fun s => by ring_nf
  refine _root_.Prove2MeSourceProof.h_b2a8a79da4bd7b154436ee26
    (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ (fun ω s => c * H ω s) hmc hpc hqc T)
    (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H hm hp hq T)
    (_root_.Prove2MeSourceProof.h_7aea30f549f53f05062f1907 W ℱ hℱ (fun ω s => c * H ω s) hmc hpc hqc hT)
    (_root_.Prove2MeSourceProof.h_7aea30f549f53f05062f1907 W ℱ hℱ H hm hp hq hT)
    (_root_.Prove2MeSourceProof.h_9ab1096355abba8f677466b8 W ℱ hℱ (fun ω s => c * H ω s) H hmc hm hpc hp
      hqc hq hT) ?_ ?_
  · rw [hscale, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg c)]
  · rw [hdiff, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg (c - 1))]
end Scaling

end LevyStochCalc.Brownian.Ito


