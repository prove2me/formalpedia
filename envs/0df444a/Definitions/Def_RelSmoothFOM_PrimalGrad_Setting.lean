-- Prove2me | Definitions.Def_RelSmoothFOM_PrimalGrad_Setting
-- name    : RelSmoothFOM_PrimalGrad_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T03:33:59.164008+00:00
-- url     : https://prove2.me/theorems/9862b747-4dc7-486a-b41b-39bd625d8f29
-- title:
--   (7), Definitions 1.1–1.2, Algorithm 1, pp. 334–337 — Bregman distance, relative smoothness and strong convexity, primal gradient runs
-- statement:
--   Let $E$ be a finite-dimensional real inner-product space, $Q\subseteq E$ a closed convex set, and $f,h:E\to\mathbb R$. In the paper’s setting, $f$ and the **reference function** $h$ are differentiable and convex on $Q$. The reference function need not be strongly or even strictly convex; these standing conditions are supplied as theorem hypotheses.
--
--   1. **Bregman distance** (7). For $x,y\in Q$,
--   $$D_h(y,x) := h(y)-h(x)-\langle\nabla h(x),\,y-x\rangle .$$
--   The derivative is taken at the second argument.
--
--   2. **Relative smoothness** (Definition 1.1). $f$ is $L$-smooth relative to $h$ on $Q$ if, for all $x,y$ in the interior of $Q$ (in the relative interior of $Q$ when $Q$ has empty interior),
--   $$f(y)\le f(x)+\langle\nabla f(x),\,y-x\rangle+L\,D_h(y,x).$$
--
--   3. **Relative strong convexity** (Definition 1.2). $f$ is $\mu$-strongly convex relative to $h$ on $Q$ if, for the same $x,y$,
--   $$f(y)\ge f(x)+\langle\nabla f(x),\,y-x\rangle+\mu\,D_h(y,x).$$
--
--   4. **Primal gradient run** (Algorithm 1). A sequence $x^0,x^1,x^2,\dots$ is a run of the primal gradient scheme with parameter $L$ if $x^0\in Q$ and, for every $i\ge 0$, $x^{i+1}\in Q$ minimises over $Q$
--   $$x\;\mapsto\; f(x^i)+\langle\nabla f(x^i),\,x-x^i\rangle+L\,D_h(x,x^i).$$
--
--   These objects carry the analysis of the primal gradient scheme. For the Euclidean reference function $h=\tfrac12\|\cdot\|^2$, Algorithm 1 becomes projected gradient descent with step $1/L$ when $L>0$.
--
--   **Formalization Note** The pairing $\langle\nabla f(x),v\rangle$ is written as the Fréchet derivative $f'(x)v$ (`fderiv ℝ f x v`), which equals the inner product with the gradient on an inner-product space. "Interior, or relative interior when there is no interior" is Mathlib's `intrinsicInterior ℝ Q`, which is the interior when that is nonempty and the relative interior otherwise. The definitions take $L$ and $\mu$ as parameters fixed before $x,y$; the condition $\mu\ge0$ of Definition 1.2 is a separate hypothesis wherever the definition is used. The total Lean Bregman function can be evaluated outside $Q$, but the paper’s analysis uses it on $Q$. The next iterate of Algorithm 1 is described by its minimising property rather than a choice function.
-- source:
--   Lu, Freund & Nesterov, Relatively smooth convex optimization by first-order methods, and applications, SIAM J. Optim. 28 (2018), pp. 334–337, (7), Definitions 1.1–1.2, Algorithm 1

import Mathlib

namespace RelSmoothFOM.PrimalGrad

/-- The Bregman distance (7): `D_h(y, x) := h(y) - h(x) - ⟨∇h(x), y - x⟩`.
The derivative is taken at the second argument `x`. -/
noncomputable def bregman {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : E → ℝ) (y x : E) : ℝ :=
  h y - h x - fderiv ℝ h x (y - x)

/-- Definition 1.1: `f` is `L`-smooth relative to `h` on `Q`, i.e. (11)
`f(y) ≤ f(x) + ⟨∇f(x), y - x⟩ + L D_h(y, x)` for all `x, y` in the interior of `Q`
(the relative interior when `Q` has no interior). -/
def IsRelSmooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : Set E) (f h : E → ℝ) (L : ℝ) : Prop :=
  ∀ x ∈ intrinsicInterior ℝ Q, ∀ y ∈ intrinsicInterior ℝ Q,
    f y ≤ f x + fderiv ℝ f x (y - x) + L * bregman h y x

/-- Definition 1.2: `f` is `μ`-strongly convex relative to `h` on `Q`, i.e. (12)
`f(y) ≥ f(x) + ⟨∇f(x), y - x⟩ + μ D_h(y, x)` for all `x, y` in the interior of `Q`
(the relative interior when `Q` has no interior). The sign condition `μ ≥ 0` of the
definition is stated separately wherever the definition is used. -/
def IsRelStronglyConvex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : Set E) (f h : E → ℝ) (μ : ℝ) : Prop :=
  ∀ x ∈ intrinsicInterior ℝ Q, ∀ y ∈ intrinsicInterior ℝ Q,
    f y ≥ f x + fderiv ℝ f x (y - x) + μ * bregman h y x

/-- Algorithm 1 (primal gradient scheme with reference function `h`), 0-based:
`x 0 ∈ Q`, and each `x (i+1)` is a minimiser over `Q` of
`u ↦ f(x^i) + ⟨∇f(x^i), u - x^i⟩ + L D_h(u, x^i)`. -/
def IsPrimalGradientRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : Set E) (f h : E → ℝ) (L : ℝ) (x : ℕ → E) : Prop :=
  x 0 ∈ Q ∧ ∀ i : ℕ, x (i + 1) ∈ Q ∧ ∀ u ∈ Q,
    f (x i) + fderiv ℝ f (x i) (x (i + 1) - x i) + L * bregman h (x (i + 1)) (x i)
      ≤ f (x i) + fderiv ℝ f (x i) (u - x i) + L * bregman h u (x i)

end RelSmoothFOM.PrimalGrad


