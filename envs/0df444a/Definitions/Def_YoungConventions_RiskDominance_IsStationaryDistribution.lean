-- Prove2me | Definitions.Def_YoungConventions_RiskDominance_IsStationaryDistribution
-- name    : YoungConventions_RiskDominance_IsStationaryDistribution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:57:06.948649+00:00
-- url     : https://prove2.me/theorems/9ee30acb-2838-4dee-91ae-23d0f73135c0
-- title:
--   Stationary distribution of a finite transition matrix
-- statement:
--   A function $\mu$ on a finite state space $X$ is a **stationary distribution** of the transition matrix $P$ if it is a probability vector that $P$ leaves invariant:
--   $$\mu_x\ge0\ \ (x\in X),\qquad\sum_{x\in X}\mu_x=1,\qquad \mu P=\mu,$$
--   with $\mu$ a row vector, i.e. $\sum_x\mu_xP_{xy}=\mu_y$ for every $y$.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §6, p. 68

import Mathlib

namespace YoungConventions.RiskDominance

/-- **Stationary distribution** of a finite transition matrix. Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §6, p. 68 (PDF p. 13): "a
unique stationary distribution `μ^ε` satisfying the equation `μ^ε P^ε = μ^ε`".

`μ` is a probability vector (nonnegative, summing to one) that is invariant: `μ P = μ`, with `μ` a
row vector. -/
def IsStationaryDistribution {X : Type*} [Fintype X] (μ : X → ℝ) (P : Matrix X X ℝ) : Prop :=
  (∀ x, 0 ≤ μ x) ∧ ∑ x, μ x = 1 ∧ Matrix.vecMul μ P = μ

end YoungConventions.RiskDominance


