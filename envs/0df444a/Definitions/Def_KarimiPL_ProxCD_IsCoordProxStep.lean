-- Prove2me | Definitions.Def_KarimiPL_ProxCD_IsCoordProxStep
-- name    : KarimiPL_ProxCD_IsCoordProxStep
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:53:51.505868+00:00
-- url     : https://prove2.me/theorems/29f947f0-8533-41d4-b909-01c607a42cbc
-- title:
--   One coordinate-wise proximal-gradient step (16)
-- statement:
--   Throughout, $\mathbb{R}^d$ carries the Euclidean inner product and norm, $e_i$ is the $i$-th unit vector, $x_i$ the $i$-th coordinate of $x$, and $\nabla_i f(x)$ the $i$-th coordinate of $\nabla f(x)$. The objective is $F = f + g$ with $f : \mathbb{R}^d \to \mathbb{R}$ differentiable and $g(x) = \sum_{i=1}^d g_i(x_i)$ separable, each $g_i : \mathbb{R} \to (-\infty, +\infty]$ convex with effective domain $D_i$; $\operatorname{dom} g = D_1 \times \dots \times D_d$.
--
--   Let $L \in \mathbb{R}$, $i$ a coordinate and $x, p \in \mathbb{R}^d$. The point $p$ is a **coordinate-wise proximal-gradient step from $x$ in coordinate $i$** if
--   $$p = x + \alpha^* e_i, \qquad \alpha^* \in \operatorname*{argmin}_\alpha \Big[\alpha \nabla_i f(x) + \frac L2 \alpha^2 + g_i(x_i + \alpha) - g_i(x_i)\Big].$$
--   This is the update (16) of Karimi, Nutini and Schmidt with $i = i_k$ and $x = x_k$ (step size $1/L$).
--
--   **Formalization Note** The printed (16) writes $x_{k+1} = \operatorname{argmin}_\alpha[\dots]$, setting a vector equal to a scalar; it is read as $x_{k+1} = x_k + \alpha^* e_{i_k}$, as in the coordinate descent update (6) and in Appendix H. The minimizer is a predicate (no existence or closedness assumed).
-- source:
--   Karimi, Nutini, Schmidt, Linear Convergence of Gradient and Proximal-Gradient Methods Under the Polyak-Łojasiewicz Condition, arXiv:1608.04636v4, §4.3, eq. (16), p. 10

import Mathlib
import Definitions.Def_KarimiPL_ProxCD_IsCoordMin

namespace KarimiPL.ProxCD

/-- **One coordinate-wise proximal-gradient step (16) in coordinate `i`.**
Karimi, Nutini, Schmidt, *Linear Convergence of Gradient and Proximal-Gradient Methods Under the
Polyak-Łojasiewicz Condition*, arXiv:1608.04636v4, §4.3, eq. (16), p. 10: "The update rule for the coordinate-wise proximal-gradient method is
xk+1 = argmin_α [α∇ik f(xk) + (L/2)α² + gik(xik + α) − gik(xik)], (16)".

`IsCoordProxStep f gc Dc L i x p` says: `p = x + α* eᵢ` for some `α*` attaining the minimum of
the bracket of (16) in coordinate `i` at `x` (`IsCoordMin`).

**Formalization Note.** The printed (16) sets the vector `x_{k+1}` equal to the minimizing
scalar `α`; it is read as `x_{k+1} = x_k + α* e_{i_k}`, as in the coordinate descent update (6)
(§3.1, p. 5) and in Appendix H (p. 23), which evaluates `F(x + yᵢeᵢ)` at the minimizing `yᵢ`.
`α eᵢ` is `EuclideanSpace.single i α`. The step size is `1/L` (the factor `L/2` in the
bracket). Existence of `α*` is part of the predicate, not assumed globally. -/
def IsCoordProxStep {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (gc : Fin d → ℝ → ℝ)
    (Dc : Fin d → Set ℝ) (L : ℝ) (i : Fin d) (x p : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∃ t : ℝ, IsCoordMin f gc Dc L i x t ∧ p = x + EuclideanSpace.single i t

end KarimiPL.ProxCD


