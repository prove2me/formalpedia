-- Prove2me | Definitions.Def_KarimiPL_ProxCD_IsProxPL
-- name    : KarimiPL_ProxCD_IsProxPL
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:52:30.460985+00:00
-- url     : https://prove2.me/theorems/4701694e-c23d-44d7-8299-facbc19563f3
-- title:
--   The proximal-PL inequality with constant $\mu$
-- statement:
--   Throughout, $\mathbb{R}^d$ carries the Euclidean inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$, $e_i$ is the $i$-th unit vector, $x_i$ the $i$-th coordinate of $x$, and $\nabla_i f(x)$ the $i$-th coordinate of $\nabla f(x)$. The composite objective is $F = f + g$ with $f : \mathbb{R}^d \to \mathbb{R}$ differentiable and $g : \mathbb{R}^d \to (-\infty, +\infty]$ extended-valued.
--
--   Let $D$ be the effective domain of $g$, $L, \mu \in \mathbb{R}$ and $x^* \in \mathbb{R}^d$, and write $F^* = F(x^*)$. The pair $(f, g)$ satisfies the **proximal-PL inequality with constant $\mu$** if $\mu > 0$ and
--   $$\frac12 \mathcal D_g(x, L) \ge \mu\big(F(x) - F^*\big)$$
--   for every $x \in D$ at which the minimum defining $\mathcal D_g(x, L)$ is attained.
--
--   This is inequality (12) of Karimi, Nutini and Schmidt, the hypothesis of Theorems 5 and 6. It generalizes the Polyak–Łojasiewicz inequality to composite problems $f + g$ with a non-smooth convex $g$.
--
--   **Formalization Note** In the theorems that use it, $x^*$ is a minimizer of $F$ over $D$, so $F^*$ is the optimal value. The inequality is imposed only at points of $D$ (off $D$ both sides of (12) are $+\infty$) and only where the minimum in $\mathcal D_g(x, L)$ exists (elsewhere the paper's $\min$ is undefined). Identical to the unpublished sibling draft `KarimiPL.ProxGrad.IsProxPL`.
-- source:
--   Karimi, Nutini, Schmidt, Linear Convergence of Gradient and Proximal-Gradient Methods Under the Polyak-Łojasiewicz Condition, arXiv:1608.04636v4, §4, eq. (12)–(13), p. 8

import Mathlib
import Definitions.Def_KarimiPL_ProxCD_IsProxGradStep
import Definitions.Def_KarimiPL_ProxCD_Dg

namespace KarimiPL.ProxCD

/-- **The proximal-PL inequality (12) with constant `μ`.**
Karimi, Nutini, Schmidt, *Linear Convergence of Gradient and Proximal-Gradient Methods Under the
Polyak-Łojasiewicz Condition*, arXiv:1608.04636v4, eq. (12), p. 8: "there exists a µ > 0
satisfying (1/2)Dg(x, L) ≥ µ(F(x) − F∗), (12) […] We call this the proximal-PL inequality".

`IsProxPL f g D L μ xstar` says: `0 < μ`, and for every `x ∈ D` at which the minimum in (13)
(with `α = L`) is attained,
`μ · (F(x) − F*) ≤ ½ Dg(x, L)`, where `F = f + g` and `F* = F(x*)`.

**Formalization Note.** `F* = f xstar + g xstar`; the theorems using this predicate assume that
`xstar ∈ D` minimizes `F` over `D`, so `F*` is the paper's optimal value. The paper's `g` is
extended-valued, encoded by its effective domain `D` and finite values `g` on `D`. The
inequality is required only at `x ∈ D`: for `x ∉ D` the paper's (12) reads `+∞ ≥ +∞` (both
sides infinite) and carries no content. It is required only where the minimum of (13) exists
(some `p` with `IsProxGradStep f g D L x p`): elsewhere the paper's `min` is undefined, and this
restriction makes `Dg` the paper's minimum at every point where it is used. The paper's
"there exists a µ > 0" is reflected by taking `μ` as a parameter with `0 < μ`, because
the rate of Theorem 6 (and Theorem 5) names that `μ`. In this mission `g = sepG gc`
and `D = sepDom Dc` (separable `g`, §4.3, p. 10). -/
def IsProxPL {d : ℕ} (f g : EuclideanSpace ℝ (Fin d) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin d))) (L μ : ℝ) (xstar : EuclideanSpace ℝ (Fin d)) : Prop :=
  0 < μ ∧ ∀ x ∈ D, (∃ p, IsProxGradStep f g D L x p) →
    μ * (f x + g x - (f xstar + g xstar)) ≤ 1 / 2 * Dg f g D L x

end KarimiPL.ProxCD


