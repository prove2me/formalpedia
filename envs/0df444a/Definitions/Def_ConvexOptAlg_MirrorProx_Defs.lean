-- Prove2me | Definitions.Def_ConvexOptAlg_MirrorProx_Defs
-- name    : ConvexOptAlg_MirrorProx_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T18:04:23.868959+00:00
-- url     : https://prove2.me/theorems/fcf7b305-669d-4d9c-9e90-2b9f98154f29
-- title:
--   Ch. 4 preamble and §§4.1, 4.5, pp. 297–305 — Bregman divergence, mirror maps, ρ-strong convexity and β-smoothness w.r.t. ‖·‖, Bregman projection, mirror prox
-- statement:
--   This module fixes the objects of Chapter 4 that mirror prox uses. Throughout, $E$ is a finite-dimensional real vector space carrying an arbitrary norm $\|\cdot\|$ (the book's $\mathbb R^n$ with a fixed norm). Gradients are linear functionals on $E$: $\nabla f(x)^\top v$ is the value of the functional $\nabla f(x)$ at $v$, and the dual norm $\|g\|_* = \sup_{\|v\|\le 1} g^\top v$ is the operator norm of $g$.
--
--   1. **Bregman divergence.** For $\Phi$ with gradient map $\nabla\Phi$,
--   $$D_\Phi(x,y)=\Phi(x)-\Phi(y)-\nabla\Phi(y)^\top(x-y).$$
--   2. **Mirror map.** Let $\mathcal D\subseteq E$ be a convex open set. A function $\Phi$ is a mirror map on $\mathcal D$ if (i) $\Phi$ is strictly convex on $\mathcal D$ and differentiable at every point of $\mathcal D$; (ii) its gradient takes all possible values: every linear functional equals $\nabla\Phi(y)$ for some $y\in\mathcal D$; (iii) its gradient diverges on the boundary: $\|\nabla\Phi(x)\|_*\to+\infty$ as $x\to z$ inside $\mathcal D$, for every boundary point $z$ of $\mathcal D$.
--   3. **Strong convexity w.r.t. $\|\cdot\|$.** $\Phi$ is $\rho$-strongly convex on a set $S$ if
--   $$\Phi(x)-\Phi(y)\le\nabla\Phi(x)^\top(x-y)-\frac\rho2\|x-y\|^2\qquad\text{for all }x,y\in S .$$
--   4. **Smoothness w.r.t. $\|\cdot\|$.** $f$ is $\beta$-smooth on $\mathcal X$ if it has a gradient $\nabla f(x)$ at every $x\in\mathcal X$ (relative to $\mathcal X$) and $\|\nabla f(x)-\nabla f(y)\|_*\le\beta\|x-y\|$ for all $x,y\in\mathcal X$.
--   5. **Bregman projection.** $z$ is a Bregman projection of $y$ onto $\mathcal X$, i.e. $z\in\Pi^\Phi_{\mathcal X}(y)=\operatorname{argmin}_{x\in\mathcal X\cap\mathcal D}D_\Phi(x,y)$, if $z\in\mathcal X\cap\mathcal D$ and $D_\Phi(z,y)\le D_\Phi(w,y)$ for every $w\in\mathcal X\cap\mathcal D$.
--   6. **Mirror prox.** Sequences $(x_t),(y_t),(y'_t),(x'_t)$ form a run of mirror prox with step size $\eta$ if $x_1\in\mathcal X\cap\mathcal D$ and, for every $t\ge1$, $y'_{t+1},x'_{t+1}\in\mathcal D$ and
--   $$\nabla\Phi(y'_{t+1})=\nabla\Phi(x_t)-\eta\nabla f(x_t),\qquad y_{t+1}\in\operatorname*{argmin}_{x\in\mathcal X\cap\mathcal D}D_\Phi(x,y'_{t+1}),$$
--   $$\nabla\Phi(x'_{t+1})=\nabla\Phi(x_t)-\eta\nabla f(y_{t+1}),\qquad x_{t+1}\in\operatorname*{argmin}_{x\in\mathcal X\cap\mathcal D}D_\Phi(x,x'_{t+1}).$$
--
--   The algorithm first makes a mirror descent step from $x_t$ to $y_{t+1}$, then a second step, again from $x_t$, with the gradient evaluated at $y_{t+1}$. These are the objects of Lemma 4.1 and Theorem 4.4 of the book.
--
--   **Formalization Note** The gradient of $\Phi$ is an explicit map `Φ'` with values in the continuous linear functionals `E →L[ℝ] ℝ`, and `HasFDerivAt Φ (Φ' x) x` for $x\in\mathcal D$; the gradient of $f$ is an explicit map `f'` with `HasFDerivWithinAt f (f' x) X x` for $x\in\mathcal X$ (the book's $f$ is a function on $\mathcal X$). Property (iii) is stated as a limit along $\mathcal D$ at each frontier point. The projection and the run are relations: every argmin choice is allowed, no choice function is used. The run does not fix $x_1$ beyond $x_1\in\mathcal X\cap\mathcal D$; theorems that need $x_1\in\operatorname{argmin}_{\mathcal X\cap\mathcal D}\Phi$ assume it. The index $0$ is unused. The conditions $\mathcal X\subseteq\overline{\mathcal D}$ and $\mathcal X\cap\mathcal D\ne\emptyset$ are hypotheses of each theorem.
-- source:
--   Bubeck, arXiv:1405.4980v2, Ch. 4 preamble, p. 297 (dual norm, β-smooth (ii), α-strongly convex (iii), Bregman divergence); §4.1, p. 298 (mirror map (i)–(iii), Π^Φ_X); §4.5, p. 305 (mirror prox equations)

import Mathlib

namespace ConvexOptAlg.MirrorProx

open Filter Topology

/-- The Bregman divergence (Bubeck, arXiv:1405.4980v2, Ch. 4 preamble, p. 297):
`D_Φ(x, y) = Φ(x) − Φ(y) − ∇Φ(y)⊤(x − y)`. The gradient `∇Φ(y)` is the continuous linear functional
`Φ' y : E →L[ℝ] ℝ`, and `∇Φ(y)⊤v` is its value `Φ' y v`. -/
def bregman {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) (x y : E) : ℝ :=
  Φ x - Φ y - Φ' y (x - y)

/-- `Φ` is a mirror map on the convex open set `D` with gradient map `Φ'`
(§4.1, p. 298): `D` is open and convex, and
(i) `Φ` is strictly convex on `D` and differentiable at every point of `D`, with derivative `Φ' x`;
(ii) the gradient takes all possible values, `∇Φ(D) = (ℝⁿ)*`: every continuous linear functional
is `Φ' y` for some `y ∈ D`;
(iii) the gradient diverges on the boundary of `D`: for every `z ∈ ∂D`,
`‖∇Φ(x)‖ → +∞` as `x → z` inside `D` (the norm of `∇Φ(x)` is the dual (operator) norm).
The set conditions `X ⊆ closure D` and `X ∩ D ≠ ∅` of §4.1 are separate hypotheses of each theorem. -/
def IsMirrorMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : Set E) (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) : Prop :=
  IsOpen D ∧ Convex ℝ D ∧ StrictConvexOn ℝ D Φ ∧
    (∀ x ∈ D, HasFDerivAt Φ (Φ' x) x) ∧
    (∀ φ : E →L[ℝ] ℝ, ∃ y ∈ D, Φ' y = φ) ∧
    (∀ z ∈ frontier D, Tendsto (fun x => ‖Φ' x‖) (𝓝[D] z) atTop)

/-- `Φ` is `ρ`-strongly convex on the set `S` w.r.t. `‖·‖`, with gradient map `Φ'`
(Ch. 4 preamble (iii), p. 297, for a differentiable function, whose only subgradient is the
gradient): `Φ(x) − Φ(y) ≤ ∇Φ(x)⊤(x − y) − (ρ/2)‖x − y‖²` for all `x, y ∈ S`.
It is used with `S = X ∩ D`. -/
def IsStronglyConvexWRT {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) (ρ : ℝ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, Φ x - Φ y ≤ Φ' x (x - y) - ρ / 2 * ‖x - y‖ ^ 2

/-- `f` is `β`-smooth on `X` w.r.t. `‖·‖`, with gradient map `f'` (Ch. 4 preamble (ii), p. 297):
`f' x` is the derivative of `f` at `x` within `X` for every `x ∈ X`, and
`‖∇f(x) − ∇f(y)‖∗ ≤ β‖x − y‖` for all `x, y ∈ X`, the dual norm `‖·‖∗` being the operator norm
on `E →L[ℝ] ℝ`. -/
def IsSmoothWRT {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (f : E → ℝ) (f' : E → E →L[ℝ] ℝ) (β : ℝ) : Prop :=
  (∀ x ∈ X, HasFDerivWithinAt f (f' x) X x) ∧
    ∀ x ∈ X, ∀ y ∈ X, ‖f' x - f' y‖ ≤ β * ‖x - y‖

/-- `z` is a Bregman projection of `y` onto `X ∩ D`: `z ∈ X ∩ D` and `z` minimizes
`w ↦ D_Φ(w, y)` over `X ∩ D` (§4.1, p. 298: `Π^Φ_X(y) = argmin_{x ∈ X ∩ D} D_Φ(x, y)`). -/
def IsBregmanProj {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X D : Set E) (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) (y z : E) : Prop :=
  z ∈ X ∩ D ∧ ∀ w ∈ X ∩ D, bregman Φ Φ' z y ≤ bregman Φ Φ' w y

/-- The sequences `(x_t, y_t, y'_t, x'_t)` form a run of mirror prox with step size `η`
(§4.5, p. 305): `x₁ ∈ X ∩ D`, and for every `t ≥ 1`
* `y'_{t+1} ∈ D` and `∇Φ(y'_{t+1}) = ∇Φ(x_t) − η∇f(x_t)`;
* `y_{t+1} ∈ argmin_{x ∈ X ∩ D} D_Φ(x, y'_{t+1})`;
* `x'_{t+1} ∈ D` and `∇Φ(x'_{t+1}) = ∇Φ(x_t) − η∇f(y_{t+1})`;
* `x_{t+1} ∈ argmin_{x ∈ X ∩ D} D_Φ(x, x'_{t+1})`.
The gradients `∇f` are given by the map `f'`. Index `0` is unused. The choice of `x₁` is not
fixed here; theorems that need `x₁ ∈ argmin_{X ∩ D} Φ` assume it. -/
def IsMirrorProxRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X D : Set E) (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) (f' : E → E →L[ℝ] ℝ) (η : ℝ)
    (x y y' x' : ℕ → E) : Prop :=
  x 1 ∈ X ∩ D ∧
    ∀ t : ℕ, 1 ≤ t →
      y' (t + 1) ∈ D ∧ Φ' (y' (t + 1)) = Φ' (x t) - η • f' (x t) ∧
      IsBregmanProj X D Φ Φ' (y' (t + 1)) (y (t + 1)) ∧
      x' (t + 1) ∈ D ∧ Φ' (x' (t + 1)) = Φ' (x t) - η • f' (y (t + 1)) ∧
      IsBregmanProj X D Φ Φ' (x' (t + 1)) (x (t + 1))

end ConvexOptAlg.MirrorProx


