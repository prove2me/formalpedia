-- Prove2me | Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansion_CollisionAnalyticHelpers
-- name    : OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansion_CollisionAnalyticHelpers
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-20T07:51:05.112995+00:00
-- url     : https://prove2.me/theorems/e9681135-bd49-4939-b319-c22f16d05574
-- title:
--   Analytic row-test helpers for period-monomial determinants
-- statement:
--   Defines the Cauchy row test, exponential monomials, and the column functions arising from period-monomial coefficient extraction, along with their differentiability.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms

open scoped BigOperators
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion

namespace OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.CollisionAnalytic

noncomputable def rowTest (ell : ℕ) (f : ℂ → ℂ) : ℂ :=
  cauchyPowerSeries f 0 (1 / 2) ell (fun _ => 1)

noncomputable def exponentialMonomial (b h : ℂ) (d : ℕ) (z : ℂ) : ℂ :=
  b * Complex.exp (h * z) * z ^ d

theorem differentiable_exponentialMonomial (b h : ℂ) (d : ℕ) :
    Differentiable ℂ (exponentialMonomial b h d) := by
  exact ((Complex.differentiable_exp.comp (differentiable_id.const_mul h)).const_mul b).mul
    (differentiable_id.pow d)

noncomputable def columnFunction {m : ℕ} (h : ℕ) (a : Fin m → ℕ)
    (A : Fin m →₀ ℕ) : ℂ → ℂ :=
  exponentialMonomial ((∏ i, (a i).choose (A i) : ℕ) : ℂ) (h : ℂ)
    (∑ i : Fin m, (a i - A i))

theorem differentiable_columnFunction {m : ℕ} (h : ℕ) (a : Fin m → ℕ)
    (A : Fin m →₀ ℕ) : Differentiable ℂ (columnFunction h a A) :=
  differentiable_exponentialMonomial _ _ _

end OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.CollisionAnalytic


