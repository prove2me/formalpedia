-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoFiltrationChange_F000
-- name    : LevyStochCalc_Brownian_ItoFiltrationChange_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:30:40.738087+00:00
-- url     : https://prove2.me/theorems/72772e21-f57b-44b0-b43e-05b97e24b718
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoFiltrationChange
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoFiltrationChange. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraAssociativity_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraAssociativity_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoDriverLinear_F000
import Definitions.Def_LevyStochCalc_Poisson_PredictableRepresentation_F000
import Definitions.Def_LevyStochCalc_Poisson_PredictableRepresentation_F001
import Definitions.Def_SourceProof_bf1e37b50d3528bd4d7f3e39

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

/-- The `L²` Brownian Itô integral agrees almost everywhere with the integral taken over the
filtration augmented by the null sets and frozen before time zero. -/
theorem stochasticIntegralBrownian_augFiltration
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
    (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hp' : Probability.ProgressivelyMeasurable (augFiltration ℱ P) H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (T : ℝ) :
    stochasticIntegralBrownian W ℱ hℱ H hm hp hq T
      =ᵐ[P] stochasticIntegralBrownian W (augFiltration ℱ P)
        (isBrownianFiltration_augFiltration hℱ) H hm hp' hq T :=
  _root_.Prove2MeSourceProof.h_bf1e37b50d3528bd4d7f3e39 W ℱ (augFiltration ℱ P) hℱ
    (isBrownianFiltration_augFiltration hℱ) (le_augFiltration ℱ P) H hm hp hp' hq T
end LevyStochCalc.Brownian.Ito

namespace LevyStochCalc.Poisson.Compensated

open MeasureTheory
open scoped NNReal ENNReal

universe u
universe v

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]

/-- Adaptedness of a mark-step integrand transfers along an inclusion of filtrations. -/
theorem MarkStep.Adapted.mono_filtration {g : TimeGrid}
    {ℱ 𝒢 : Filtration ℝ ‹MeasurableSpace Ω›} {G : MarkStep Ω E ν g}
    (hG : G.Adapted ℱ) (hle : ∀ t, ℱ t ≤ 𝒢 t) : G.Adapted 𝒢 :=
  fun i hi k => (hG i hi k).mono (hle _)
/-- The stage tolerances `((n : ℝ≥0∞) + 1)⁻¹` tend to zero. -/
theorem tendsto_natCast_add_one_inv :
    Filter.Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹) Filter.atTop (nhds 0) := by
  have hg : Filter.Tendsto (fun n : ℕ => n + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun n => Nat.le_succ n) Filter.tendsto_id
  have h := ENNReal.tendsto_inv_nat_nhds_zero.comp hg
  refine h.congr (fun n => ?_)
  simp [Nat.cast_add_one]
end LevyStochCalc.Poisson.Compensated


