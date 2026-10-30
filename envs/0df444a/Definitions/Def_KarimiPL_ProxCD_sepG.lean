-- Prove2me | Definitions.Def_KarimiPL_ProxCD_sepG
-- name    : KarimiPL_ProxCD_sepG
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:51:07.800251+00:00
-- url     : https://prove2.me/theorems/9a749cb0-3f1b-414a-977d-8deff7852067
-- title:
--   Separable function $g(x) = \sum_i g_i(x_i)$ (finite part)
-- statement:
--   Throughout, $\mathbb{R}^d$ carries the Euclidean inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$, $e_i$ is the $i$-th unit vector, $x_i$ the $i$-th coordinate of $x$, and $\nabla_i f(x)$ the $i$-th coordinate of $\nabla f(x)$. The composite objective is $F = f + g$ with $f : \mathbb{R}^d \to \mathbb{R}$ differentiable and $g : \mathbb{R}^d \to (-\infty, +\infty]$ extended-valued.
--
--   Let $g_1, \dots, g_d$ be univariate functions, each $g_i : \mathbb{R} \to (-\infty, +\infty]$ given by its effective domain $D_i \subseteq \mathbb{R}$ and its finite values $g_i$ on $D_i$. The **separable function** they define is
--   $$g(x) = \sum_{i=1}^d g_i(x_i), \qquad x \in \mathbb{R}^d .$$
--   On the effective domain $D_1 \times \dots \times D_d$ (see the companion definition of $\operatorname{dom} g$) this is the finite value of $g$; off it the paper's $g$ is $+\infty$.
--
--   This is the structural assumption of §4.3 of Karimi, Nutini and Schmidt under which proximal coordinate descent converges linearly (Theorem 6). Typical examples are $g(x) = \lambda\|x\|_1$ and the indicator of a box.
--
--   **Formalization Note** Each $g_i$ is a real function `gc i : ℝ → ℝ` whose values off `Dc i` are never used by the theorems.
-- source:
--   Karimi, Nutini, Schmidt, Linear Convergence of Gradient and Proximal-Gradient Methods Under the Polyak-Łojasiewicz Condition, arXiv:1608.04636v4, §4.3, p. 10

import Mathlib

namespace KarimiPL.ProxCD

/-- **A separable function `g(x) = ∑ᵢ gᵢ(xᵢ)` (finite part).**
Karimi, Nutini, Schmidt, *Linear Convergence of Gradient and Proximal-Gradient Methods Under the
Polyak-Łojasiewicz Condition*, arXiv:1608.04636v4, §4.3, p. 10: "we require the extra assumption that g is a separable function. This means
that g(x) = Σi gi(xi) for a set of univariate functions gi".

`sepG gc x = ∑ i, gc i (x i)`.

**Formalization Note.** The paper's `gᵢ : ℝ → (−∞, ∞]` (indicators are allowed, §4, p. 8) is
encoded by its effective domain `Dc i : Set ℝ` (see `sepDom`) and its finite values
`gc i : ℝ → ℝ` on `Dc i`. On `dom g = sepDom Dc` the value `sepG gc x` is the paper's `g(x)`;
values off `dom g` are never used by the theorems. `ℝᵈ` is `EuclideanSpace ℝ (Fin d)` and
`x i` is the `i`-th coordinate. -/
def sepG {d : ℕ} (gc : Fin d → ℝ → ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i, gc i (x i)

end KarimiPL.ProxCD


