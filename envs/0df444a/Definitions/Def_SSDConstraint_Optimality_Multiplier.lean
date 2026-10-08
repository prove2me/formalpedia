-- Prove2me | Definitions.Def_SSDConstraint_Optimality_Multiplier
-- name    : SSDConstraint_Optimality_Multiplier
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T08:08:47.985424+00:00
-- url     : https://prove2.me/theorems/2cc8e11d-a5a8-4ed5-a9a8-b0cb052785da
-- title:
--   The measure Lagrangian $\Lambda(X,\mu)$ (4.4) and the utility function of a measure (p. 9)
-- statement:
--   Fix problem data as in (3.1)–(3.3) with interval $[a,b]$, and let $G(X)(\eta)=F_2(Y;\eta)-F_2(X;\eta)$ for $\eta\in[a,b]$.
--
--   1. For a measure $\mu$ on $[a,b]$ (extended to $\mathbb R$ by assigning measure $0$ to sets not meeting $[a,b]$), the **Lagrangian** (4.4) is
--   $$\Lambda(X,\mu)=f(X)+\int_a^b G(X)(\eta)\,d\mu(\eta),$$
--   the integral being over the closed interval $[a,b]$.
--   2. With every nonnegative measure $\mu$ one associates the function
--   $$u(t)=\begin{cases}-\displaystyle\int_t^b\mu([\tau,b])\,d\tau, & t<b,\\[2pt] 0, & t\ge b.\end{cases}$$
--
--   These are the objects through which the paper passes from the abstract Lagrange multiplier in the dual of $\mathcal C([a,b])$ to a utility function in $\mathcal U_1$.
--
--   **Formalization Note** Multiplier measures are Borel measures on $\mathbb R$; the theorems that use them assume they are finite and give zero mass to the complement of $[a,b]$. The integral in (4.4) is a set integral over `Set.Icc a b`, so atoms at $a$ and $b$ count. $\mu([\tau,b])$ is computed as a real number (`μ.real`), which is the true value for a finite measure.
-- source:
--   Dentcheva and Ruszczyński, Optimization with stochastic dominance constraints, preprint dated December 27, 2002 (SPEPS; published SIAM J. Optim. 14(2), 2003), p. 8, (4.4), and p. 9, the function u associated with a nonnegative measure

import Mathlib
import Definitions.Def_SSDConstraint_Optimality_Problem

namespace SSDConstraint.Optimality

open MeasureTheory

/-- The measure-space Lagrangian (4.4), p. 8: for a measure `μ` on `[a, b]` (extended by zero to `ℝ`),
`Λ(X, μ) = f(X) + ∫_a^b G(X)(η) dμ(η)` with `G(X)(η) = F₂(Y; η) − F₂(X; η)`. The integral is over the
closed interval `[a, b]`, so atoms at `a` and `b` count. -/
noncomputable def Problem.Lambda {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (pr : Problem Ω P) (X : Ω →₁[P] ℝ) (μ : Measure ℝ) : ℝ :=
  pr.f X + ∫ η in Set.Icc pr.a pr.b, (F2 P pr.Y η - F2 P X η) ∂μ

/-- The utility function associated with a nonnegative measure `μ`, p. 9:
`u(t) = −∫_t^b μ([τ, b]) dτ` for `t < b`, and `u(t) = 0` for `t ≥ b`. -/
noncomputable def uOfMeasure (μ : Measure ℝ) (b : ℝ) (t : ℝ) : ℝ :=
  if t < b then -∫ τ in t..b, μ.real (Set.Icc τ b) else 0

end SSDConstraint.Optimality


