-- Prove2me | Definitions.Def_RiskAverseConsistency_IsConvexRiskMeasure
-- name    : RiskAverseConsistency_IsConvexRiskMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:21:00.58021+00:00
-- url     : https://prove2.me/theorems/771fd278-220f-47be-ba04-20c05c913b52
-- title:
--   Convex risk measure on $L^p(\Omega,\mathcal F,P)$: (R1)–(R3)
-- statement:
--   A functional $\rho:L^p(\Omega,\mathcal F,P)\to\mathbb R$ is a **convex risk measure** if it satisfies
--
--   1. (R1) convexity: $\rho(\lambda X+(1-\lambda)Y)\le\lambda\rho(X)+(1-\lambda)\rho(Y)$ for all $X,Y\in L^p$ and $\lambda\in(0,1)$;
--   2. (R2) monotonicity: $\rho(X)\le\rho(Y)$ whenever $X\le Y$ with probability one;
--   3. (R3) translation equivariance: $\rho(X+C)=\rho(X)+c$ whenever $C\in L^p$ equals the constant $c\in\mathbb R$ with probability one.
--
--   This is the class of risk functionals for which the paper proves consistency of empirical approximations.
--
--   **Formalization Note** The paper allows values in $(-\infty,\infty]$; every result of the paper that uses the notion takes $\rho$ real-valued, which is the type here. No normalization $\rho(0)=0$ and no positive homogeneity (R4) is imposed.
-- source:
--   Milz, Surowiec, Asymptotic consistency for nonconvex risk-averse stochastic optimization with infinite dimensional decision spaces, arXiv:2207.14756v2, pp.4–5, §2.2, conditions (R1)–(R3) and the definition of a convex risk measure

import Mathlib

open MeasureTheory

namespace RiskAverseConsistency

/-- A real-valued functional `ρ : Lᵖ(Ω, F, P) → ℝ` is a **convex risk measure**: it satisfies
(R1) convexity, (R2) monotonicity and (R3) translation equivariance.

Milz, Surowiec, arXiv:2207.14756v2, §2.2, pp.4–5, conditions (R1)–(R3) and "The risk measure ρ is
called convex if it satisfies (R1)–(R3)".

Formalization Note: the paper allows `ρ : Lᵖ → (−∞, ∞]`; every result of the paper that uses this
notion takes `ρ` real-valued, which is the type here. No normalization `ρ(0) = 0` and no positive
homogeneity (R4) are imposed. In (R3) the degenerate random variable `C` is any element of `Lᵖ` that
equals the constant `c` almost surely, as on the page. -/
def IsConvexRiskMeasure {Ω : Type*} [MeasurableSpace Ω] {p : ENNReal} {P : Measure Ω}
    (ρ : Lp ℝ p P → ℝ) : Prop :=
  (∀ (X Y : Lp ℝ p P) (lam : ℝ), 0 < lam → lam < 1 →
      ρ (lam • X + (1 - lam) • Y) ≤ lam * ρ X + (1 - lam) * ρ Y) ∧
  (∀ X Y : Lp ℝ p P, (∀ᵐ ω ∂P, X ω ≤ Y ω) → ρ X ≤ ρ Y) ∧
  (∀ (X C : Lp ℝ p P) (c : ℝ), (∀ᵐ ω ∂P, C ω = c) → ρ (X + C) = ρ X + c)

end RiskAverseConsistency


