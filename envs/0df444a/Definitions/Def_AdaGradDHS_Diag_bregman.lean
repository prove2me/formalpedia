-- Prove2me | Definitions.Def_AdaGradDHS_Diag_bregman
-- name    : AdaGradDHS_Diag_bregman
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:15:02.429986+00:00
-- url     : https://prove2.me/theorems/424193e5-06ec-4ba6-ae83-f007b588deb3
-- title:
--   Bregman divergence $B_\psi(x,y)$
-- statement:
--   Let $\psi : \mathbb{R}^d \to \mathbb{R}$. The **Bregman divergence** of $\psi$ between $x, y \in \mathbb{R}^d$ is
--   $$B_\psi(x, y) = \psi(x) - \psi(y) - \langle \nabla\psi(y),\, x - y\rangle .$$
--
--   It measures how far $\psi$ lies above its linearization at $y$. The composite mirror-descent update (4) uses $B_{\psi_t}(x, x_t)$ as its proximal term, and the regret bounds for that update are written in terms of Bregman divergences.
--
--   **Formalization Note** $\nabla$ is Mathlib's `gradient`, which is $0$ at points where $\psi$ is not differentiable. Every statement of the mission that uses $B_\psi$ either assumes $\psi$ differentiable at the relevant points or uses the AdaGrad proximal function, which is a quadratic polynomial.
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), §1.1, p. 2122 (unnumbered definition of B_ψ)

import Mathlib

namespace AdaGradDHS.Diag

/-- **Bregman divergence `B_ψ(x, y) = ψ(x) − ψ(y) − ⟨∇ψ(y), x − y⟩`.**
Duchi, Hazan, Singer, *Adaptive Subgradient Methods for Online Learning and Stochastic
Optimization*, JMLR 12 (2011), §1.1, p. 2122 (unnumbered): "Bψ(x, y) = ψ(x) − ψ(y) − ⟨∇ψ(y), x − y⟩".

`bregman ψ x y` is `ψ x − ψ y − ⟨∇ψ(y), x − y⟩` on `ℝ^d = EuclideanSpace ℝ (Fin d)`.

**Formalization Note.** `∇` is Mathlib's `gradient`, which is `0` at points where `ψ` is not
differentiable. Every statement of this mission that uses `bregman ψ` either assumes `ψ`
differentiable at the relevant points (`IsOneStronglyConvexWrt`) or uses the polynomial
`adagradPsi`, which is differentiable everywhere. -/
noncomputable def bregman {d : ℕ} (ψ : EuclideanSpace ℝ (Fin d) → ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ψ x - ψ y - inner ℝ (gradient ψ y) (x - y)

end AdaGradDHS.Diag


