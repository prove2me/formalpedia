-- Prove2me | Definitions.Def_KarimiPL_ProxCD_coordModel
-- name    : KarimiPL_ProxCD_coordModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:52:48.153132+00:00
-- url     : https://prove2.me/theorems/2451aad5-8d80-417f-8167-d6f9b1ee7dbe
-- title:
--   Coordinate model of proximal coordinate descent: $\alpha\nabla_i f(x) + \frac L2\alpha^2 + g_i(x_i+\alpha) - g_i(x_i)$
-- statement:
--   Throughout, $\mathbb{R}^d$ carries the Euclidean inner product and norm, $e_i$ is the $i$-th unit vector, $x_i$ the $i$-th coordinate of $x$, and $\nabla_i f(x)$ the $i$-th coordinate of $\nabla f(x)$. The objective is $F = f + g$ with $f : \mathbb{R}^d \to \mathbb{R}$ differentiable and $g(x) = \sum_{i=1}^d g_i(x_i)$ separable, each $g_i : \mathbb{R} \to (-\infty, +\infty]$ convex with effective domain $D_i$; $\operatorname{dom} g = D_1 \times \dots \times D_d$.
--
--   For $L \in \mathbb{R}$, a coordinate $i$, a point $x$ and $t \in \mathbb{R}$, the **coordinate model** is
--   $$m_i(x; t) = t\,\nabla_i f(x) + \frac{L}{2} t^2 + g_i(x_i + t) - g_i(x_i).$$
--   It is the bracket minimized in the coordinate-wise proximal-gradient update (16) of Karimi, Nutini and Schmidt (with $\alpha = t$), and the right-hand side of the upper bound (62) on $F(x + t e_i) - F(x)$.
--
--   **Formalization Note** $g_i$ is given by its finite values `gc i`; the model is the paper's bracket whenever $x_i, x_i + t \in D_i$ (it is $+\infty$ when $x_i + t \notin D_i$, which the step predicate excludes).
-- source:
--   Karimi, Nutini, Schmidt, Linear Convergence of Gradient and Proximal-Gradient Methods Under the Polyak-Łojasiewicz Condition, arXiv:1608.04636v4, §4.3, eq. (16), p. 10; Appendix H, eq. (62), p. 23

import Mathlib

namespace KarimiPL.ProxCD

/-- **The coordinate model of the update (16): the bracket `α∇ᵢf(x) + (L/2)α² + gᵢ(xᵢ + α) − gᵢ(xᵢ)`.**
Karimi, Nutini, Schmidt, *Linear Convergence of Gradient and Proximal-Gradient Methods Under the
Polyak-Łojasiewicz Condition*, arXiv:1608.04636v4, §4.3, eq. (16), p. 10:
"xk+1 = argmin_α [α∇ik f(xk) + (L/2)α² + gik(xik + α) − gik(xik)], (16)";
also the right-hand side of (62), Appendix H, p. 23.

`coordModel f gc L i x t = t · ∇ᵢf(x) + (L/2) t² + gcᵢ(xᵢ + t) − gcᵢ(xᵢ)`.

**Formalization Note.** `∇ᵢf(x)` is the `i`-th coordinate `gradient f x i` of Mathlib's
`gradient`; `ℝᵈ` is `EuclideanSpace ℝ (Fin d)`. The paper's extended-valued `gᵢ` is encoded by
its effective domain `Dc i` and finite values `gc i`; this real-valued model is the paper's
bracket whenever `xᵢ` and `xᵢ + t` lie in `Dc i` (it is `+∞` in the paper when
`xᵢ + t ∉ Dc i`, which `IsCoordMin` excludes). The constant `− gᵢ(xᵢ)` of the bracket is kept. -/
noncomputable def coordModel {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (gc : Fin d → ℝ → ℝ)
    (L : ℝ) (i : Fin d) (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) : ℝ :=
  t * gradient f x i + L / 2 * t ^ 2 + gc i (x i + t) - gc i (x i)

end KarimiPL.ProxCD


