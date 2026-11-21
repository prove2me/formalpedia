-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_PRPPairing_F001
-- name    : LevyStochCalc_Brownian_PRPPairing_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:54:39.458819+00:00
-- url     : https://prove2.me/theorems/46e4b7e6-e8ef-4d1a-86ef-b0c8337a784e
-- title:
--   Source declarations: LevyStochCalc.Brownian.PRPPairing
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.PRPPairing. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_PRPPairing_F000

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

/-- The time-integral term of Itô's formula for a trigonometric function of a process. -/
noncomputable def trigDrift (l : ℝ) (g : ℝ → ℝ) (X : ℝ → Ω → ℝ) (a b t : ℝ) (ω : Ω) : ℝ :=
  1 / 2 * ∫ s in Set.Ioc (0 : ℝ) t, -l ^ 2 * g (X s ω) * indIoc Ω a b ω s ^ 2 ∂volume
/-- The drift term, with the indicator's idempotence used and the constants pulled out. -/
theorem trigDrift_eq (l : ℝ) {g : ℝ → ℝ} (X : ℝ → Ω → ℝ) (a b t : ℝ) (ω : Ω) :
    trigDrift l g X a b t ω
      = -(l ^ 2 / 2) * ∫ s in Set.Ioc (0 : ℝ) t, g (X s ω) * indIoc Ω a b ω s ∂volume := by
  rw [trigDrift]
  simp only [indIoc_sq]
  rw [← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  ring
end Equation

end LevyStochCalc.Brownian.Ito


