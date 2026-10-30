-- Prove2me | Definitions.Def_KarimiPL_ProxCD_IsCoordMin
-- name    : KarimiPL_ProxCD_IsCoordMin
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:53:17.283094+00:00
-- url     : https://prove2.me/theorems/99c645e8-a21b-438f-addb-6a62d85524de
-- title:
--   Coordinate minimizer of the proximal coordinate model
-- statement:
--   Throughout, $\mathbb{R}^d$ carries the Euclidean inner product and norm, $e_i$ is the $i$-th unit vector, $x_i$ the $i$-th coordinate of $x$, and $\nabla_i f(x)$ the $i$-th coordinate of $\nabla f(x)$. The objective is $F = f + g$ with $f : \mathbb{R}^d \to \mathbb{R}$ differentiable and $g(x) = \sum_{i=1}^d g_i(x_i)$ separable, each $g_i : \mathbb{R} \to (-\infty, +\infty]$ convex with effective domain $D_i$; $\operatorname{dom} g = D_1 \times \dots \times D_d$.
--
--   Let $L \in \mathbb{R}$, $i$ a coordinate and $x \in \mathbb{R}^d$. A number $t$ is a **coordinate minimizer at $x$ in coordinate $i$** if $x_i + t \in D_i$ and
--   $$t\,\nabla_i f(x) + \frac{L}{2} t^2 + g_i(x_i + t) - g_i(x_i) \;\le\; u\,\nabla_i f(x) + \frac{L}{2} u^2 + g_i(x_i + u) - g_i(x_i)$$
--   for every $u$ with $x_i + u \in D_i$; that is, $t$ attains the $\operatorname{argmin}_\alpha$ in the update (16) of Karimi, Nutini and Schmidt (the bracket is $+\infty$ when $x_i + u \notin D_i$).
--
--   **Formalization Note** The argmin is a predicate: neither existence of a minimizer nor closedness or lower semicontinuity of $g_i$ is assumed. For $L > 0$ the bracket is strongly convex on its domain, so the minimizer is unique when it exists.
-- source:
--   Karimi, Nutini, Schmidt, Linear Convergence of Gradient and Proximal-Gradient Methods Under the Polyak-Łojasiewicz Condition, arXiv:1608.04636v4, §4.3, eq. (16), p. 10; Appendix H, p. 23

import Mathlib
import Definitions.Def_KarimiPL_ProxCD_coordModel

namespace KarimiPL.ProxCD

/-- **`t` attains the minimum over `α` of the bracket of (16) in coordinate `i`.**
Karimi, Nutini, Schmidt, *Linear Convergence of Gradient and Proximal-Gradient Methods Under the
Polyak-Łojasiewicz Condition*, arXiv:1608.04636v4, §4.3, eq. (16), p. 10:
"xk+1 = argmin_α [α∇ik f(xk) + (L/2)α² + gik(xik + α) − gik(xik)]"; Appendix H, p. 23:
"the coordinate descent step chooses yi to minimize this upper bound".

`IsCoordMin f gc Dc L i x t` says: `xᵢ + t ∈ Dc i`, and
`coordModel f gc L i x t ≤ coordModel f gc L i x u` for every `u` with `xᵢ + u ∈ Dc i`.

**Formalization Note.** The paper's `gᵢ` is `+∞` off its effective domain `Dc i`, so the
bracket is `+∞` when `xᵢ + u ∉ Dc i` and the minimum ranges over `xᵢ + u ∈ Dc i`. The argmin is
a predicate, not a function: neither existence of a minimizer nor closedness or lower
semicontinuity of `gᵢ` is assumed. For `L > 0` and convex `gᵢ` the bracket is strongly convex
on its domain, so the minimizer is unique when it exists. -/
def IsCoordMin {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (gc : Fin d → ℝ → ℝ)
    (Dc : Fin d → Set ℝ) (L : ℝ) (i : Fin d) (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) : Prop :=
  x i + t ∈ Dc i ∧ ∀ u : ℝ, x i + u ∈ Dc i → coordModel f gc L i x t ≤ coordModel f gc L i x u

end KarimiPL.ProxCD


