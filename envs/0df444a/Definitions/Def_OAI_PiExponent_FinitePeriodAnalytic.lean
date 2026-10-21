-- Prove2me | Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic
-- name    : OAI_PiExponent_FinitePeriodAnalytic
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-20T07:37:31.871876+00:00
-- url     : https://prove2.me/theorems/ca0f1bbf-7649-465f-9c9d-bf2969cb7125
-- title:
--   Cauchy row tests and entire columns for the actual finite period model
-- statement:
--   Defines the Cauchy coefficient functional at radius one half and the entire binomial-exponential function associated with a transverse coefficient, while reusing the existing actual period model.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open scoped BigOperators

namespace OAI.PiExponent.FinitePeriodCollision

/-- The normalized Taylor coefficient, measured on the circle of radius 1/2. -/
noncomputable def rowTest (ell : ℕ) (f : ℂ → ℂ) : ℂ :=
  cauchyPowerSeries f 0 (1 / 2) ell (fun _ => 1)

/-- The entire column function obtained after taking a transverse coefficient. -/
noncomputable def analyticColumn {m : ℕ} (h : ℕ)
    (a A : Fin m → ℕ) (z : ℂ) : ℂ :=
  ((∏ i, (a i).choose (A i) : ℕ) : ℂ) *
    Complex.exp ((h : ℂ) * z) * z ^ (∑ i, (a i - A i))

end OAI.PiExponent.FinitePeriodCollision


