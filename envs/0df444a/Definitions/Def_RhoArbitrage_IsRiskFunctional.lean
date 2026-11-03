-- Prove2me | Definitions.Def_RhoArbitrage_IsRiskFunctional
-- name    : RhoArbitrage_IsRiskFunctional
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:24:47.27731+00:00
-- url     : https://prove2.me/theorems/8314166a-fc54-4672-8ad6-6507416d3ecc
-- title:
--   Risk functional: monotone, normalised, star-shaped
-- statement:
--   A **risk functional** on $L$ is a map $\rho:L\to(-\infty,\infty]$ such that:
--
--   1. (Monotonicity) for all $X_1,X_2\in L$ with $X_1\le X_2$ $\mathbb P$-a.s., $\rho(X_1)\ge\rho(X_2)$;
--   2. (Normalisation) $\rho(0)=0$;
--   3. (Star-shapedness) for all $X\in L$ and $\lambda\in[1,\infty)$, $\rho(\lambda X)\ge\lambda\rho(X)$.
--
--   Convex normalised functionals are star-shaped, and so are positively homogeneous ones. Neither convexity, nor cash-invariance, nor positive homogeneity is assumed: Value at Risk, for example, is covered.
--
--   **Formalization Note** Lean types $\rho$ on all functions $\Omega\to\mathbb R$ with values in `EReal` and constrains it only on $L$, where it must differ from $-\infty$.
-- source:
--   Herdegen, Khan, ρ-arbitrage and ρ-consistent pricing for star-shaped risk measures, arXiv:2202.07610v3, §2.1, p.4

import Mathlib

open MeasureTheory

namespace RhoArbitrage

/-- **Risk functional.** Herdegen–Khan, arXiv:2202.07610v3, §2.1, p.4: a risk functional is a map
`ρ : L → (-∞, ∞]` with

* Monotonicity: for `X₁, X₂ ∈ L` with `X₁ ≤ X₂` `P`-a.s., `ρ(X₁) ≥ ρ(X₂)`;
* Normalisation: `ρ(0) = 0`;
* Star-shapedness: for all `X ∈ L` and `λ ∈ [1, ∞)`, `ρ(λX) ≥ λρ(X)`.

**Formalization Note.** `ρ` is typed on all of `Ω → ℝ` with values in `EReal`; only its values on
`L` are constrained, and the value set `(-∞, ∞]` is the clause `ρ X ≠ ⊥` on `L`. Monotonicity is
under `P`-a.s. inequality as printed, so `ρ` takes equal values on `P`-a.s. equal members of `L`.
The product `λρ(X)` is `(lam : EReal) * ρ X` with `lam ≥ 1` real, which sends `⊤` to `⊤`. -/
structure IsRiskFunctional {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (L : Set (Ω → ℝ))
    (ρ : (Ω → ℝ) → EReal) : Prop where
  /-- `ρ` takes values in `(-∞, ∞]` on `L`. -/
  ne_bot : ∀ X ∈ L, ρ X ≠ ⊥
  /-- Monotonicity. -/
  monotone : ∀ X₁ ∈ L, ∀ X₂ ∈ L, X₁ ≤ᵐ[P] X₂ → ρ X₂ ≤ ρ X₁
  /-- Normalisation. -/
  normalised : ρ 0 = 0
  /-- Star-shapedness. -/
  star_shaped : ∀ X ∈ L, ∀ lam : ℝ, 1 ≤ lam → (lam : EReal) * ρ X ≤ ρ (lam • X)

end RhoArbitrage


