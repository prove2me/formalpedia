-- Prove2me | Definitions.Def_RhoArbitrage_SensitiveToLargeExpectedLossesOn
-- name    : RhoArbitrage_SensitiveToLargeExpectedLossesOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:24:47.75225+00:00
-- url     : https://prove2.me/theorems/f89ebe2b-ef89-43d1-b6ce-2d01780222b9
-- title:
--   Sensitivity to large expected losses on $\mathcal Y\subset L$
-- statement:
--   Let $\mathcal A_\rho:=\{X\in L:\rho(X)\le0\}$ be the acceptance set of $\rho$. The functional $\rho$ satisfies **sensitivity to large expected losses on** $\mathcal Y\subset L$ if for each $X\in\mathcal Y\setminus\{0\}$ with $\mathbb E[X]\le0$ there is $\lambda\in(0,\infty)$ such that
--
--   $$
--   \lambda X\notin\mathcal A_\rho .
--   $$
--
--   Every nonzero position with nonpositive expected value thus becomes unacceptable once it is scaled enough. This is the axiom that drives the existence of optimal portfolios.
--
--   **Formalization Note** "$X\neq0$" is $\neg(X=0\ \mathbb P\text{-a.s.})$, because the paper's elements are a.s. classes. Since $\lambda X\in L$, the condition $\lambda X\notin\mathcal A_\rho$ is written $0<\rho(\lambda X)$.
-- source:
--   Herdegen, Khan, ρ-arbitrage and ρ-consistent pricing for star-shaped risk measures, arXiv:2202.07610v3, Definition 3.6, p.7

import Mathlib

open MeasureTheory

namespace RhoArbitrage

/-- **Sensitivity to large expected losses on `𝒴 ⊂ L`.** Herdegen–Khan, arXiv:2202.07610v3,
Definition 3.6, p.7: for each `X ∈ 𝒴 \ {0}` with `E[X] ≤ 0`, there exists `λ ∈ (0, ∞)` such that
`λX ∉ 𝒜_ρ`, where `𝒜_ρ := {X ∈ L : ρ(X) ≤ 0}` is the acceptance set (p.4).

**Formalization Note.** Since `L` is a linear space and `𝒴 ⊂ L`, `λX ∈ L`, so `λX ∉ 𝒜_ρ` is
`0 < ρ (lam • X)`. "`X ≠ 0`" is `¬ (X =ᵐ[P] 0)`, because the elements of the paper's `L` are
`P`-a.s. classes: a pointwise `X ≠ 0` would ask `ρ(λX) > 0` also of a function that is a.s. zero,
which monotonicity and normalisation rule out, and the condition would be unsatisfiable. -/
def SensitiveToLargeExpectedLossesOn {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (𝒴 : Set (Ω → ℝ)) (ρ : (Ω → ℝ) → EReal) : Prop :=
  ∀ X ∈ 𝒴, ¬ (X =ᵐ[P] 0) → ∫ ω, X ω ∂P ≤ 0 → ∃ lam : ℝ, 0 < lam ∧ 0 < ρ (lam • X)

end RhoArbitrage


