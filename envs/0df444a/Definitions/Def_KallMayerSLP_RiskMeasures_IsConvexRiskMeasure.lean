-- Prove2me | Definitions.Def_KallMayerSLP_RiskMeasures_IsConvexRiskMeasure
-- name    : KallMayerSLP_RiskMeasures_IsConvexRiskMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:40:05.516864+00:00
-- url     : https://prove2.me/theorems/d57f8abb-1d7b-46e0-acf2-f20af80d9117
-- title:
--   Convex risk measure, axioms (7.3)
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and $\Upsilon$ a linear space of real random variables on it. A function $\rho:\Upsilon\to\mathbb R$ is a **convex risk measure** (Föllmer and Schied) if for all $\vartheta,\vartheta_1,\vartheta_2\in\Upsilon$ and every real $C$:
--
--   1. (F1) $\rho$ is a convex function on $\Upsilon$ (convexity);
--   2. (F2) if $\vartheta_1\le\vartheta_2$ then $\rho(\vartheta_1)\le\rho(\vartheta_2)$ (monotonicity);
--   3. (F3) $\rho(\vartheta+C)=\rho(\vartheta)+C$ (translation invariance).
--
--   Every coherent risk measure is convex, and a convex risk measure is coherent if it is positively homogeneous.
--
--   **Formalization Note** As for coherent risk measures, $\Upsilon$ is a submodule of the functions $\Omega\to\mathbb R$, only the values of $\rho$ on $\Upsilon$ matter, and the order in (F2) is almost sure.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §7.1, (7.3), p.183 (PDF 193)

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace KallMayerSLP.RiskMeasures

/-- **Convex risk measure** (Föllmer–Schied axioms (7.3), loss convention).
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §7.1, (7.2) and (7.3), p.183 (PDF 193). The axioms are required "for any
`ϑ, ϑ₁, ϑ₂ ∈ Υ` and `λ, C ∈ ℝ, λ ≥ 0`", for a function `ρ : Υ → ℝ` on a linear space `Υ` of
random variables on a probability space `(Ω, 𝓕, P)`, representing losses.

* (F1) `ρ` is a convex function on `Υ` (convexity);
* (F2) if `ϑ₁ ≤ ϑ₂` then `ρ(ϑ₁) ≤ ρ(ϑ₂)` (monotonicity);
* (F3) `ρ(ϑ + C) = ρ(ϑ) + C` for `C ∈ ℝ` (translation invariance).

**Formalization Note.** `Υ` is a submodule of the functions `Ω → ℝ` and `ρ` is a function on
all of `Ω → ℝ` of which only the values on `Υ` matter. The hypothesis `ϑ₁ ≤ ϑ₂` of monotonicity is
taken almost surely (`ϑ₁ ≤ ϑ₂` `P`-a.s.); this is weaker than the pointwise hypothesis used in the
book's proof of Prop. 7.3 (B) ("`ϑ₁(ω) ≤ ϑ₂(ω)` for all `ω`"), so the predicate implies the
pointwise one. `ϑ + C` adds the constant random variable `C`. Convexity is `ConvexOn ℝ univ` of the restriction of `ρ` to `Υ`. -/
def IsConvexRiskMeasure {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Υ : Submodule ℝ (Ω → ℝ)) (ρ : (Ω → ℝ) → ℝ) : Prop :=
  ConvexOn ℝ Set.univ (fun ϑ : Υ => ρ ϑ) ∧
  (∀ ϑ₁ ∈ Υ, ∀ ϑ₂ ∈ Υ, ϑ₁ ≤ᵐ[P] ϑ₂ → ρ ϑ₁ ≤ ρ ϑ₂) ∧
  (∀ ϑ ∈ Υ, ∀ C : ℝ, ρ (ϑ + fun _ => C) = ρ ϑ + C)

end KallMayerSLP.RiskMeasures


