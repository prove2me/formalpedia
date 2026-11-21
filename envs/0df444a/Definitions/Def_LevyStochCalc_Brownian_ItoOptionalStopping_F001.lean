-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoOptionalStopping_F001
-- name    : LevyStochCalc_Brownian_ItoOptionalStopping_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:02:50.955164+00:00
-- url     : https://prove2.me/theorems/e0fbd6e0-d39d-4f4c-8336-e292153d4f9a
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoOptionalStopping
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoOptionalStopping. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoOptionalStopping_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Optional stopping for the Itô integral, for a stopping time of finite range

Cutting the integrand off at a stopping time that takes finitely many values below the horizon
subtracts, for each of those values `c`, the increment of the integral across `(c, T]` weighted
by the event `{τ = c}`. That weight is known at `c` and the cut integrand is carried by `(c, T]`,
so it passes inside the integral; the resulting sum telescopes into the integral evaluated at
`τ ∧ T`.

## Main statements

* `LevyStochCalc.Brownian.Ito.hitInd`, `cutTerm` — the weight and the cut integrand.
* `LevyStochCalc.Brownian.Ito.stopped_eq_sub_sum` — the pathwise decomposition of the cut
  integrand.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped` — the identity.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Stopped

variable (τ : Ω → WithTop ℝ)

section Identity

variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in
/-- The window cut is invisible at the horizon. -/
theorem stochasticIntegralBrownian_indTerm_zero {t : ℝ} (ht : 0 < t) {K : Ω → ℝ → ℝ}
    (hmK : Measurable (Function.uncurry K)) (hpK : Probability.ProgressivelyMeasurable ℱ K)
    (hqK : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hmW : Measurable (Function.uncurry (indTerm K 0 t)))
    (hpW : Probability.ProgressivelyMeasurable ℱ (indTerm K 0 t))
    (hqW : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖indTerm K 0 t ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    stochasticIntegralBrownian W ℱ hℱ (indTerm K 0 t) hmW hpW hqW t
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ K hmK hpK hqK t := by
  filter_upwards [_root_.Prove2MeSourceProof.h_371bbffaec7b2a5d68568212 W ℱ hℱ K hmK hpK hqK
      (le_refl (0 : ℝ)) ht hmW hpW hqW ht,
    _root_.Prove2MeSourceProof.h_39285c9e8cb91346b858af97 W ℱ hℱ K hmK hpK hqK (le_refl (0 : ℝ))]
    with ω hloc hz
  have hloc' : stochasticIntegralBrownian W ℱ hℱ (indTerm K 0 t) hmW hpW hqW t ω
      = stochasticIntegralBrownian W ℱ hℱ K hmK hpK hqK (min t t) ω
        - stochasticIntegralBrownian W ℱ hℱ K hmK hpK hqK (min 0 t) ω := hloc
  rw [hloc', min_self, min_eq_left ht.le, hz]
  simp
end Identity

end Stopped

end LevyStochCalc.Brownian.Ito


