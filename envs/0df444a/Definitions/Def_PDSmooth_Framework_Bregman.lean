-- Prove2me | Definitions.Def_PDSmooth_Framework_Bregman
-- name    : PDSmooth_Framework_Bregman
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:22.135862+00:00
-- url     : https://prove2.me/theorems/c0f435d0-70ad-4464-85e0-bfdd47b5b9e4
-- title:
--   §2.2–2.4, §4, pp. 9–10, 13 — Bregman divergence (2.4), Bregman proximal objective (4.1)/(4.4) and Bregman proximal points (2.9)/(4.5)
-- statement:
--   Let $\mathbb{X}$ be a real normed space and $\omega:\mathbb{X}\to\mathbb{R}$ a function. At a point $u$ where $\omega$ is (Fréchet) differentiable with derivative $\nabla\omega(u)\in\mathbb{X}^*$, the **Bregman divergence** of $\omega$ is
--
--   $$
--   D_\omega(u',u) := \omega(u') - \omega(u) - \langle \nabla\omega(u),\, u'-u\rangle, \qquad u'\in\mathbb{X}.
--   $$
--
--   Given a function $h:\mathbb{X}\to\mathbb{R}$, a step size $\lambda$ and a centre $x$, the **Bregman proximal objective** is
--
--   $$
--   Q^\lambda(x';x) := h(x') + \lambda^{-1} D_\omega(x',x),
--   $$
--
--   and, for a set $\mathcal X\subseteq\mathbb{X}$, a point $p$ is a **Bregman proximal point** $p=\mathrm{prox}(h,x,\lambda)$ when $p\in\mathcal X$ and $p$ minimizes $Q^\lambda(\cdot\,;x)$ over $\mathcal X$:
--
--   $$
--   Q^\lambda(p;x) \le Q^\lambda(x';x)\qquad\text{for all } x'\in\mathcal X .
--   $$
--
--   These are the general objects behind the non-Euclidean proximal-point method: with $\omega=\tfrac12\|\cdot\|^2$ on a Hilbert space, $D_\omega(u',u)=\tfrac12\|u'-u\|^2$ and $\mathrm{prox}$ is the usual proximal map.
--
--   **Formalization Note** The derivative is Mathlib's `fderiv`, which is $0$ at points of non-differentiability; every theorem of this mission uses $D_\omega(\cdot,u)$ only at points $u$ where differentiability of $\omega$ is assumed. The proximal point is a predicate (`IsProx`) rather than a function, so its existence and uniqueness are never presupposed: theorems either quantify over such points or assert that one exists.
-- source:
--   Zhao, A primal-dual smoothing framework for max-structured non-convex optimization, arXiv:2003.04375v5, pp. 9–10, 13, (2.4), (2.8)–(2.9), (4.1), (4.4)–(4.5)

import Mathlib

namespace PDSmooth.Framework

/-- (2.4), p. 9: the Bregman divergence of `ω`,
`D_ω(u', u) = ω(u') − ω(u) − ⟨∇ω(u), u' − u⟩`, with `∇ω(u)` the Fréchet derivative of `ω` at `u`.
It is used only at points `u` where `ω` is differentiable. -/
noncomputable def bregman {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ω : E → ℝ) (u' u : E) : ℝ :=
  ω u' - ω u - fderiv ℝ ω u (u' - u)

/-- (4.1)/(4.4), p. 13: the proximal objective `Q^λ(x'; x) = h(x') + λ⁻¹ D_ω(x', x)`. -/
noncomputable def Qprox {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h ω : E → ℝ) (lam : ℝ) (x x' : E) : ℝ :=
  h x' + lam⁻¹ * bregman ω x' x

/-- (2.9)/(4.5), pp. 10, 13: `p` is a Bregman proximal point `prox(h, x, λ)`, i.e. `p ∈ X` and `p`
minimizes `x' ↦ h(x') + λ⁻¹ D_ω(x', x)` over `X`. -/
def IsProx {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h ω : E → ℝ) (X : Set E) (lam : ℝ) (x p : E) : Prop :=
  p ∈ X ∧ ∀ x' ∈ X, Qprox h ω lam x p ≤ Qprox h ω lam x x'

end PDSmooth.Framework


