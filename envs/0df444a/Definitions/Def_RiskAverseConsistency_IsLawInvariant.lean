-- Prove2me | Definitions.Def_RiskAverseConsistency_IsLawInvariant
-- name    : RiskAverseConsistency_IsLawInvariant
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:21:13.15351+00:00
-- url     : https://prove2.me/theorems/12446eb1-6de4-44c6-812f-a60e118de19f
-- title:
--   Law invariant functional on $L^p(\Omega,\mathcal F,P)$
-- statement:
--   Two random variables $X_1,X_2\in L^p(\Omega,\mathcal F,P)$ are **distributionally equivalent** if $P(X_1\le t)=P(X_2\le t)$ for every $t\in\mathbb R$. A functional $\rho$ on $L^p(\Omega,\mathcal F,P)$ is **law invariant** if $\rho(X_1)=\rho(X_2)$ for all distributionally equivalent $X_1,X_2$.
--
--   Law invariance is what makes $\rho$ a function of the distribution function $H_X$ alone, so that empirical distribution functions can be plugged in.
-- source:
--   Milz, Surowiec, Asymptotic consistency for nonconvex risk-averse stochastic optimization with infinite dimensional decision spaces, arXiv:2207.14756v2, p.3, §2.1

import Mathlib

open MeasureTheory

namespace RiskAverseConsistency

/-- A functional `ρ` on `Lᵖ(Ω, F, P)` is **law invariant** with respect to `P`: `ρ(X₁) = ρ(X₂)`
whenever `X₁` and `X₂` are distributionally equivalent, i.e. `P(X₁ ≤ t) = P(X₂ ≤ t)` for all
`t ∈ ℝ`.

Milz, Surowiec, arXiv:2207.14756v2, §2.1, p.3. -/
def IsLawInvariant {Ω : Type*} [MeasurableSpace Ω] {p : ENNReal} {P : Measure Ω} {β : Type*}
    (ρ : Lp ℝ p P → β) : Prop :=
  ∀ X₁ X₂ : Lp ℝ p P, (∀ t : ℝ, P {ω | X₁ ω ≤ t} = P {ω | X₂ ω ≤ t}) → ρ X₁ = ρ X₂

end RiskAverseConsistency


