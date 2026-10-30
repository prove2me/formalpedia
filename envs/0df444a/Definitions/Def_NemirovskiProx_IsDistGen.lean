-- Prove2me | Definitions.Def_NemirovskiProx_IsDistGen
-- name    : NemirovskiProx_IsDistGen
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:43:44.20511+00:00
-- url     : https://prove2.me/theorems/8223d4ae-9d8d-43ea-bbbb-3d12342542d3
-- title:
--   Continuously differentiable $\alpha$-strongly convex $\omega$ on $Z$, (2.2)
-- statement:
--   Let $Z\subset E$ and let $\|\cdot\|$ be a norm on $E$. A function $\omega:Z\to\mathbb R$ with derivative field $\omega':Z\to E$ is a **continuously differentiable function that is strongly convex with modulus $\alpha$** (with respect to $\|\cdot\|$) if $\alpha>0$, $\omega'(z)$ is the gradient of $\omega$ at $z$ relative to $Z$ for every $z\in Z$, $\omega'$ is continuous on $Z$, and
--   $$\langle \omega'(z)-\omega'(w),\,z-w\rangle\ \ge\ \alpha\|z-w\|^2\qquad\forall z,w\in Z. \tag{2.2}$$
--
--   This is the distance-generating function of the prox-method: the prox-mapping, the function $H_u$ and the quantity $\Theta(z_0)$ are all built from $\omega$.
--
--   **Formalization Note** $\omega$ and $\omega'$ are functions on all of $E$ and only their values on $Z$ enter. "Continuously differentiable on $Z$" is encoded as a gradient within $Z$ at every point of $Z$ together with continuity of $\omega'$ on $Z$; neither an open neighbourhood of $Z$ nor an interior point is required. The paper's additional requirement that problems $\min_{z\in Z}[\omega(z)+\langle e,z\rangle]$ be easy to solve is computational and is not part of the definition. Mathlib's gradient needs $E$ complete, which holds in finite dimension.
-- source:
--   Nemirovski, Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems, SIAM J. Optim. 15(1) (2004), 229–251, doi:10.1137/S1052623403425629, §2.2, eq. (2.2), p. 232

import Mathlib

open scoped InnerProductSpace

namespace NemirovskiProx

/-- **Continuously differentiable `α`-strongly convex function `ω` on `Z`, (2.2).**
Nemirovski, *Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with
Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems*,
SIAM J. Optim. 15(1) (2004), §2.2, (2.2), p. 232: "Let us fix a continuously differentiable function ω(z) : Z → R
which is strongly convex, ⟨ω′(z) − ω′(w), z − w⟩ ≥ α‖z − w‖² ∀z, w ∈ Z [α > 0]".

`IsDistGen Z N α ω ω'` says: `0 < α`; at every `z ∈ Z`, `ω' z` is a gradient of `ω` at `z`
within `Z`; `ω'` is continuous on `Z`; and (2.2) holds with the norm `N`.

**Formalization Note.** `ω` and `ω'` are functions on all of `E`; only their values on `Z`
enter. "Continuously differentiable on `Z`" is encoded as a gradient field within `Z`,
continuous on `Z`: no differentiability on an open set and no interior point of `Z` is
required. The paper's ω′ is such a field. `[CompleteSpace E]` is needed by Mathlib's gradient
and holds for every finite-dimensional `E`. The paper's further requirement that problems
min_{z∈Z}[ω(z) + ⟨e, z⟩] be easy to solve is computational and is not a hypothesis. -/
def IsDistGen {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Z : Set E) (N : Seminorm ℝ E) (α : ℝ) (ω : E → ℝ) (ω' : E → E) : Prop :=
  0 < α ∧ (∀ z ∈ Z, HasGradientWithinAt ω (ω' z) Z z) ∧ ContinuousOn ω' Z ∧
    ∀ z ∈ Z, ∀ w ∈ Z, α * N (z - w) ^ 2 ≤ ⟪ω' z - ω' w, z - w⟫_ℝ

end NemirovskiProx


