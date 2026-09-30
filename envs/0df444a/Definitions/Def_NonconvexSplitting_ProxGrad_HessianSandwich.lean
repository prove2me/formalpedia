-- Prove2me | Definitions.Def_NonconvexSplitting_ProxGrad_HessianSandwich
-- name    : NonconvexSplitting_ProxGrad_HessianSandwich
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T19:06:15.099792+00:00
-- url     : https://prove2.me/theorems/73309729-ad76-47f5-96f4-b323872ff476
-- title:
--   Condition (44): $-\ell I \preceq \nabla^2 h + \nabla^2 q \preceq \ell I$
-- statement:
--   Let $h, q : \mathbb{R}^n \to \mathbb{R}$ be twice differentiable and $\ell \in \mathbb{R}$. The pair $(h, q)$ satisfies **condition (44)** with constant $\ell$ if, for every $x \in \mathbb{R}^n$,
--   $$
--   -\ell I \preceq \nabla^2 h(x) + \nabla^2 q(x) \preceq \ell I ,
--   $$
--   where $A \preceq B$ is the Loewner order: $B - A$ is symmetric and positive semidefinite.
--
--   With $q$ convex, this condition bounds only the curvature of $h$ after its concave part has been offset by $q$; the constant $\ell$ can be smaller than the Lipschitz modulus of $\nabla h$.
--
--   **Formalization Note** The Loewner order is Mathlib's partial order on continuous linear self-maps of a Hilbert space, `A ≤ B ↔ (B - A).IsPositive`, where `IsPositive` includes symmetry. Both sides of (44) are kept.
-- source:
--   Li & Pong, Global Convergence of Splitting Methods for Nonconvex Composite Optimization, arXiv:1407.0753v6, p. 18, Eq. (44)

import Mathlib
import Definitions.Def_NonconvexSplitting_ProxGrad_StandingAssumptions

namespace NonconvexSplitting.ProxGrad

/-- Condition (44) of Li–Pong (p. 18): for all `x`, `-ℓ I ⪯ ∇²h(x) + ∇²q(x) ⪯ ℓ I` in the
Loewner order (`A ≤ B` iff `B - A` is symmetric positive semidefinite). -/
def HessianSandwich {n : ℕ} (h q : EuclideanSpace ℝ (Fin n) → ℝ) (ℓ : ℝ) : Prop :=
  ∀ x, -(ℓ • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) ≤
      hess h x + hess q x ∧
    hess h x + hess q x ≤ ℓ • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))

end NonconvexSplitting.ProxGrad


