-- Prove2me | Definitions.Def_SourceProof_bf1e37b50d3528bd4d7f3e39
-- name    : SourceProof_bf1e37b50d3528bd4d7f3e39
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:27:30.871209+00:00
-- url     : https://prove2.me/theorems/75e6815f-5a7f-4641-9463-55747bb6f931
-- title:
--   LevyStochCalc source module: SourceProof_bf1e37b50d3528bd4d7f3e39
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_filtration` comes from the `LevyStochCalc.Brownian.ItoFiltrationChange` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraAssociativity_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraAssociativity_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoDriverLinear_F000
import Definitions.Def_LevyStochCalc_Poisson_PredictableRepresentation_F000
import Definitions.Def_LevyStochCalc_Poisson_PredictableRepresentation_F001
import Definitions.Def_SourceProof_39285c9e8cb91346b858af97
import Definitions.Def_SourceProof_7e6dc0a5b3abba2670f5e8de

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The stochastic integrals under a change of filtration

The `L²` Brownian Itô integral and the `L²` Itô–Lévy integral against a compensated Poisson
random measure are each assembled from an approximating sequence of elementary integrands
selected relative to a filtration, so one integrand integrated against one driver over two
filtrations gives two constructions. The elementary integral of such an approximant mentions no
filtration, and the `L²` distance between two elementary integrals, or between an elementary
integral and the limit, is the energy of the difference of the integrands; both constructions
are therefore the `L²`-limit of a single sequence, and they agree almost everywhere. Passing to
the augmented filtration is the case of interest, since that filtration satisfies the usual
conditions.

## Main statements

* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_filtration` — the Brownian
  integral over `ℱ` agrees almost everywhere with the integral over a larger filtration.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_augFiltration` — the Brownian integral
  over `ℱ` agrees almost everywhere with the integral over `augFiltration ℱ P`.
* `LevyStochCalc.Poisson.Compensated.process_congr_filtration`,
  `LevyStochCalc.Poisson.Compensated.stochasticIntegral_congr_filtration`,
  `LevyStochCalc.Poisson.Compensated.stochasticIntegral_augFiltration` — the same three
  statements for the compensated Poisson integral.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]


theorem _root_.Prove2MeSourceProof.h_bf1e37b50d3528bd4d7f3e39
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ 𝒢 : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : IsBrownianFiltration W ℱ) (h𝒢 : IsBrownianFiltration W 𝒢)
    (hle : ∀ t, ℱ t ≤ 𝒢 t) (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
    (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hp' : Probability.ProgressivelyMeasurable 𝒢 H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (T : ℝ) :
    stochasticIntegralBrownian W ℱ hℱ H hm hp hq T
      =ᵐ[P] stochasticIntegralBrownian W 𝒢 h𝒢 H hm hp' hq T := by
  rcases le_or_gt T 0 with hT | hT
  · exact (_root_.Prove2MeSourceProof.h_39285c9e8cb91346b858af97 W ℱ hℱ H hm hp hq hT).trans
      (_root_.Prove2MeSourceProof.h_39285c9e8cb91346b858af97 W 𝒢 h𝒢 H hm hp' hq hT).symm
  have hSm : ∀ n : ℕ,
      AEStronglyMeasurable (LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n) T) P := by
    intro n
    refine (Finset.measurable_sum _ fun k _ => ?_).aestronglyMeasurable
    exact ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n).ξ_measurable k).mul
      ((W.measurable_eval _).sub (W.measurable_eval _))
  have hIf : AEStronglyMeasurable (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq T) P :=
    ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H hm hp hq T).mono
      (ℱ.le T)).aestronglyMeasurable
  have hIg : AEStronglyMeasurable (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W 𝒢 h𝒢 H hm hp' hq T) P :=
    ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted W 𝒢 h𝒢 H hm hp' hq T).mono
      (𝒢.le T)).aestronglyMeasurable
  have hFf := _root_.Prove2MeSourceProof.h_2554b195ead815ae5442020c W ℱ hℱ H hm hp hq hT.le
  have hiso : ∀ n : ℕ,
      eLpNorm (fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n) T ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq T ω) 2 P
        = eLpNorm (fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n) T ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W 𝒢 h𝒢 H hm hp' hq T ω) 2 P := by
    intro n
    have h1 : ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n) T ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        = ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n) T ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W 𝒢 h𝒢 H hm hp' hq T ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
      rw [LevyStochCalc.Brownian.Ito.isometry_simple_sub_stochasticIntegralBrownian W ℱ hℱ (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n)
          (LevyStochCalc.Brownian.Ito.masterApprox_adapt ℱ H hm hp hq n) H hm hp hq hT,
        LevyStochCalc.Brownian.Ito.isometry_simple_sub_stochasticIntegralBrownian W 𝒢 h𝒢 (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n)
          (fun i => (LevyStochCalc.Brownian.Ito.masterApprox_adapt ℱ H hm hp hq n i).mono (hle _)) H hm hp' hq hT]
    have hsq : eLpNorm (fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n) T ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq T ω) 2 P ^ (2 : ℝ)
        = eLpNorm (fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n) T ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W 𝒢 h𝒢 H hm hp' hq T ω) 2 P ^ (2 : ℝ) := by
      rw [LevyStochCalc.Brownian.Ito.eLpNorm_two_rpow_eq_lintegral_sq, LevyStochCalc.Brownian.Ito.eLpNorm_two_rpow_eq_lintegral_sq]
      exact h1
    exact ENNReal.rpow_left_injective (by norm_num : (2 : ℝ) ≠ 0) hsq
  exact _root_.Prove2MeSourceProof.h_7e6dc0a5b3abba2670f5e8de hSm hIf hIg hFf (hFf.congr hiso)
end LevyStochCalc.Brownian.Ito


