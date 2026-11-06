-- Prove2me | Definitions.Def_SilverRateSC_IsLocalComponent
-- name    : SilverRateSC_IsLocalComponent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:45:28.829948+00:00
-- url     : https://prove2.me/theorems/bbf5b195-0d68-4603-b9e7-c2a7c39a9fee
-- title:
--   Local hard function: nonnegative, convex, $1$-smooth, $\partial_Y\Phi\le0$, zero for $X\le\ell_i$, $Y\ge0$
-- statement:
--   A function $\Phi:\mathbb R^2\to\mathbb R$ is a **local hard function with input threshold $\ell_i$** if it is nonnegative, convex and $1$-smooth (differentiable with $1$-Lipschitz gradient), satisfies $\partial_Y\Phi\le0$ everywhere, and
--   $$\Phi(X,Y)=0\qquad\text{whenever }X\le\ell_i,\ Y\ge0.$$
--   The companion predicate `IsFlatAbove` says $\partial_Y\Phi(X,Y)=0$ for all $X\in\mathbb R$, $Y\ge\ell_{i+1}$.
--
--   These are the common properties asserted in Lemmas 3.1–3.3 for the bending, repair and bridging components.
--
--   **Formalization Note** "Convex and $1$-smooth" is the published `KatyushaNs.IsConvexLSmooth 1`; $\partial_Y$ is the second coordinate of the gradient.
-- source:
--   Liu, Ye, Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case, arXiv:2609.26873 (sha256 1e325f28…), Lemmas 3.1–3.3, pp.15–16

import Mathlib
import Definitions.Def_KatyushaNs_IsConvexLSmooth

namespace SilverRateSC

/-- **A local hard function with input threshold `ℓ_i`**: `Φ : ℝ² → ℝ` is nonnegative, convex
and `1`-smooth, `∂_YΦ ≤ 0` everywhere, and `Φ(X, Y) = 0` whenever `X ≤ ℓ_i`, `Y ≥ 0`.

Liu, Ye, *Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case*,
arXiv:2609.26873, Lemmas 3.1–3.3, pp. 15–16 (the common first sentence of the three lemmas).

**Formalization Note** `ℝ²` is `EuclideanSpace ℝ (Fin 2)` with coordinates `(X, Y)`; `∂_YΦ` is
coordinate `1` of Mathlib's `gradient`. "Convex and `1`-smooth" is the published
`KatyushaNs.IsConvexLSmooth 1 Φ` (convex, differentiable, `1`-Lipschitz gradient), so the gradient
is the true one. -/
def IsLocalComponent (Φ : EuclideanSpace ℝ (Fin 2) → ℝ) (ℓ : ℝ) : Prop :=
  (∀ z, 0 ≤ Φ z) ∧ KatyushaNs.IsConvexLSmooth 1 Φ ∧ (∀ z, gradient Φ z 1 ≤ 0) ∧
    ∀ X Y : ℝ, X ≤ ℓ → 0 ≤ Y → Φ !₂[X, Y] = 0

/-- `∂_YΦ(X, Y) = 0` for all `X ∈ ℝ`, `Y ≥ ℓ_{i+1}` (Lemmas 3.1 and 3.3). -/
def IsFlatAbove (Φ : EuclideanSpace ℝ (Fin 2) → ℝ) (ℓ' : ℝ) : Prop :=
  ∀ X Y : ℝ, ℓ' ≤ Y → gradient Φ !₂[X, Y] 1 = 0

end SilverRateSC


