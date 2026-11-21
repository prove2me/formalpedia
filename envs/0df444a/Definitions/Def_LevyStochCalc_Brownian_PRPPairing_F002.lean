-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_PRPPairing_F002
-- name    : LevyStochCalc_Brownian_PRPPairing_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:52:21.393126+00:00
-- url     : https://prove2.me/theorems/21af3d2b-6ad5-4dd4-ae2b-dac7a41670c6
-- title:
--   Source declarations: LevyStochCalc.Brownian.PRPPairing
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.PRPPairing. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Analysis_GronwallIntegral_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoPullOut_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoTrigIncrement_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Pairing a weight orthogonal to the Itô integrals against a trigonometric increment

If `Z` pairs to zero against every Itô integral, then pairing it against `g (X_t)`, for `X` a
version of `∫ 1_{(a,b]} dW` and `g` one of the scaled trigonometric functions, gives a scalar
function of `t` that solves `Λ(t) = −(l²/2) ∫_0^t 1_{(a,b]}(s) Λ(s) ds`. Grönwall then forces
`Λ` to vanish.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Pairing

variable {P : Measure Ω} [IsProbabilityMeasure P]

variable {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}

variable {a b : ℝ}
  {hm : Measurable (Function.uncurry (indIoc Ω a b))}
  {hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b)}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X : ℝ → Ω → ℝ}

end Pairing

section Perp

variable {P : Measure Ω} [IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}
  {a b : ℝ}

end Perp

section Equation

variable {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- The pairing vanishes at time zero when the weight has mean zero. -/
theorem pairing_zero_time {X : ℝ → Ω → ℝ} (hX0 : X 0 =ᵐ[P] fun _ => (0 : ℝ))
    {Y : Ω → ℂ} (hY0 : ∫ ω, Y ω ∂P = 0) (g : ℝ → ℝ) :
    ∫ ω, Y ω * ((g (X 0 ω) : ℝ) : ℂ) ∂P = 0 := by
  have hcong : ∫ ω, Y ω * ((g (X 0 ω) : ℝ) : ℂ) ∂P = ∫ ω, Y ω * ((g 0 : ℝ) : ℂ) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hX0] with ω hω
    rw [hω]
  rw [hcong, integral_mul_const, hY0, zero_mul]
end Equation

end LevyStochCalc.Brownian.Ito


