-- Prove2me | Definitions.Def_WassersteinDRO_ConvexLossP1_conjugate
-- name    : WassersteinDRO_ConvexLossP1_conjugate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:51:00.3431+00:00
-- url     : https://prove2.me/theorems/760595d7-0d0b-4148-97ad-6f73c31dea9a
-- title:
--   Convex conjugate $\ell^*(z)$
-- statement:
--   Let $(E, \|\cdot\|)$ be a finite-dimensional real normed space with dual space $E^*$, and let $\ell : E \to [-\infty, +\infty]$. The **conjugate** of $\ell$ is the function $\ell^* : E^* \to [-\infty, +\infty]$,
--   $$\ell^*(z) = \sup_{\xi \in E} \big( z(\xi) - \ell(\xi) \big).$$
--   The dual norm of $z$ is $\|z\|_* = \sup_{\|\xi\| \le 1} z(\xi)$.
--
--   On $\mathbb R^m$ the pairing $z(\xi)$ is $z^\top \xi$. Eq. (13) of the paper expresses the Lipschitz modulus of a convex loss through the domain $\{z : \ell^*(z) < \infty\}$ of its conjugate.
--
--   **Formalization Note** Dual vectors are continuous linear functionals `StrongDual ℝ E` and $\|z\|_*$ is their operator norm. Points with $\ell(\xi) = +\infty$ contribute $-\infty$ to the supremum and points with $\ell(\xi) = -\infty$ contribute $+\infty$.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2, Notation, p. 8

import Mathlib

namespace WassersteinDRO.ConvexLossP1

/-- **The convex conjugate `ℓ*(z)`.**
Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, arXiv:1908.08729v2, Notation, p. 8: "The conjugate of a function ℓ(ξ) on R^m is defined as
ℓ∗(z) = sup_ξ z^⊤ξ − ℓ(ξ). … If ‖ξ‖ represents the norm of ξ ∈ R^m, then ‖z‖∗ = sup_{‖ξ‖≤1} z^⊤ξ
denotes the corresponding dual norm."

`conjugate ℓ z` is `sup_{ξ ∈ E} (z(ξ) − ℓ(ξ)) ∈ [−∞, ∞]` for a continuous linear functional `z`.

**Formalization Note.** The pairing `z^⊤ξ` of `ℝ^m` with itself is the evaluation `z ξ` of
`z : StrongDual ℝ E` (every linear functional on a finite-dimensional space is continuous), and the
paper's dual norm `‖z‖∗ = sup_{‖ξ‖≤1} z^⊤ξ` is the operator norm `‖z‖`. Points with `ℓ(ξ) = +∞`
contribute `−∞` (EReal: `c − ⊤ = ⊥`) and points with `ℓ(ξ) = −∞` contribute `+∞`. -/
noncomputable def conjugate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (ℓ : E → EReal)
    (z : StrongDual ℝ E) : EReal :=
  ⨆ ξ : E, ((z ξ : ℝ) : EReal) - ℓ ξ

end WassersteinDRO.ConvexLossP1


