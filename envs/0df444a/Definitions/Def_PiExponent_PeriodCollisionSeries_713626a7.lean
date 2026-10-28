-- Prove2me | Definitions.Def_PiExponent_PeriodCollisionSeries_713626a7
-- name    : PiExponent_PeriodCollisionSeries_713626a7
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-24T18:26:38.956776+00:00
-- url     : https://prove2.me/theorems/262bb97e-0b99-4b2a-a95e-2763dedf8dee
-- title:
--   Normalized Cauchy factors for period coefficients
-- statement:
--   Defines the logarithmic row tests, the entire binomial exponential monomial for a transverse coefficient, and its Taylor coefficients scaled by a positive radius.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Definitions.Def_PiExponent_FiniteTranslationData_690acb6f
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

open scoped BigOperators

namespace OAI.PiExponent.PeriodCollisionSeries_713626a7

/-- The normalized Cauchy test applied to a translated logarithmic power. -/
noncomputable def rowFactor (R : ℝ) (j ell d : ℕ) : ℂ :=
  cauchyPowerSeries
    (fun t : ℂ => (((j : ℂ) *
      FiniteMinorAnalysis_690acb6f.period + Complex.log (1 + t)) / (R : ℂ)) ^ d)
    0 (1 / 2) ell (fun _ => 1)

/-- The entire exponential monomial belonging to a transverse coefficient.
The binomial factor makes this zero if any coordinate of A exceeds a. -/
noncomputable def columnFunction {m : ℕ} (h : ℕ) (a : Fin m → ℕ)
    (A : Fin m →₀ ℕ) (z : ℂ) : ℂ :=
  ((∏ i, (a i).choose (A i) : ℕ) : ℂ) *
    Complex.exp ((h : ℂ) * z) * z ^ (∑ i, (a i - A i))

/-- Taylor coefficients scaled by the radius R, represented by Cauchy tests. -/
noncomputable def columnFactor {m : ℕ} (R : ℝ) (h : ℕ) (a : Fin m → ℕ)
    (A : Fin m →₀ ℕ) (d : ℕ) : ℂ :=
  cauchyPowerSeries (columnFunction h a A) 0 R d (fun _ => (R : ℂ))

end OAI.PiExponent.PeriodCollisionSeries_713626a7


