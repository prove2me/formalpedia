-- Prove2me | Definitions.Def_GallegoOzerADI_PositiveSetup_ABConvex
-- name    : GallegoOzerADI_PositiveSetup_ABConvex
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:44:16.367487+00:00
-- url     : https://prove2.me/theorems/004d3efb-0ba3-4f6a-9ed8-87dc9d610229
-- title:
--   Definition 1 — $(a,b)$-convex functions $C(a,b)$
-- statement:
--   Let $a \ge 0$ and $b \ge 0$. A function $g : \mathbb{R} \to \mathbb{R}$ is called **$(a,b)$-convex**, written $g \in C(a,b)$, if
--
--   $$
--   g(\theta x_1 + (1-\theta)x_2) \le \theta\bigl(a + g(x_1)\bigr) + (1-\theta)\bigl(b + g(x_2)\bigr)
--   \quad\text{for all } x_1 \le x_2 \text{ and } \theta \in [0,1].
--   $$
--
--   Geometrically, $g \in C(a,b)$ if and only if the segment joining $(x_1, g(x_1) + a)$ and $(x_2, g(x_2) + b)$ lies in the epigraph of $g$ whenever $x_1 \le x_2$. The class $C(0,0)$ consists of the convex functions, and $C(0,K)$ is Scarf's class of $K$-convex functions, the tool behind the optimality of $(s,S)$ policies in inventory problems with a set-up cost $K$.
--
--   **Formalization Note** The inequality is imposed only for ordered pairs $x_1 \le x_2$; when $a \ne b$ this is not the same as imposing it for all pairs. The paper defines the class only for $a, b \ge 0$; the predicate itself does not carry these sign conditions, and every theorem that uses it states them as hypotheses.
-- source:
--   Gallego, Özer, Integrating Replenishment Decisions with Advance Demand Information, Management Science 47(10):1344–1360 (2001), p. 1349, Definition 1

import Mathlib

namespace GallegoOzerADI.PositiveSetup

/-- Definition 1 (Gallego–Özer 2001, p. 1349): for `a ≥ 0`, `b ≥ 0`, a function `g : ℝ → ℝ` is
`(a, b)`-convex, `g ∈ C(a, b)`, if
`g (θ x₁ + (1 - θ) x₂) ≤ θ (a + g x₁) + (1 - θ) (b + g x₂)` for all `x₁ ≤ x₂` and `θ ∈ [0, 1]`.
The inequality is required only for ordered pairs `x₁ ≤ x₂`; `(0, K)`-convexity is Scarf's
`K`-convexity. The nonnegativity of `a` and `b` is the paper's standing requirement on the
parameters and is carried as a hypothesis by every theorem that uses this class. -/
def ABConvex (a b : ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ x₁ x₂ : ℝ, x₁ ≤ x₂ → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
    g (θ * x₁ + (1 - θ) * x₂) ≤ θ * (a + g x₁) + (1 - θ) * (b + g x₂)

end GallegoOzerADI.PositiveSetup


