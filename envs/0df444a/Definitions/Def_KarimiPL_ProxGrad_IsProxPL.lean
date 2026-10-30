-- Prove2me | Definitions.Def_KarimiPL_ProxGrad_IsProxPL
-- name    : KarimiPL_ProxGrad_IsProxPL
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:55:46.153446+00:00
-- url     : https://prove2.me/theorems/1f2f76e8-85e0-4108-96f9-a353fa93e7a9
-- title:
--   The proximal-PL inequality with constant $\mu$
-- statement:
--   Throughout, $\mathbb{R}^d$ carries the Euclidean inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$. The composite objective is $F = f + g$, where $f : \mathbb{R}^d \to \mathbb{R}$ is differentiable and $g : \mathbb{R}^d \to (-\infty, +\infty]$ is extended-valued with effective domain $D = \{x : g(x) < +\infty\}$.
--
--   Let $L, \mu \in \mathbb{R}$ and $x^* \in \mathbb{R}^d$, and write $F^* = F(x^*)$. The pair $(f, g)$ satisfies the **proximal-PL inequality with constant $\mu$** if $\mu > 0$ and
--   $$\frac12 \mathcal D_g(x, L) \ge \mu\big(F(x) - F^*\big)$$
--   for every $x \in D$ at which the minimum defining $\mathcal D_g(x, L)$ is attained.
--
--   This is inequality (12) of Karimi, Nutini and Schmidt. It generalizes the Polyak–Łojasiewicz inequality to composite problems $f + g$ with a non-smooth convex $g$, and it is the hypothesis under which the proximal-gradient method converges linearly (Theorem 5).
--
--   **Formalization Note** In the theorems that use it, $x^*$ is a minimizer of $F$ over $D$, so $F^*$ is the optimal value. The inequality is imposed only at points of $D$ (off $D$ both sides of (12) are $+\infty$) and only where the minimum in $\mathcal D_g(x, L)$ exists (elsewhere the paper's $\min$ is undefined). The constant $\mu$ is a parameter rather than existentially quantified, because Theorem 5's rate uses it.
-- source:
--   Karimi, Nutini, Schmidt, Linear Convergence of Gradient and Proximal-Gradient Methods Under the Polyak-Łojasiewicz Condition, arXiv:1608.04636v4, §4, eq. (12)–(13), p. 8

import Mathlib
import Definitions.Def_KarimiPL_ProxGrad_IsProxGradStep
import Definitions.Def_KarimiPL_ProxGrad_Dg

namespace KarimiPL.ProxGrad

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
Theorem 5's conclusion names that `μ`. -/
def IsProxPL {d : ℕ} (f g : EuclideanSpace ℝ (Fin d) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin d))) (L μ : ℝ) (xstar : EuclideanSpace ℝ (Fin d)) : Prop :=
  0 < μ ∧ ∀ x ∈ D, (∃ p, IsProxGradStep f g D L x p) →
    μ * (f x + g x - (f xstar + g xstar)) ≤ 1 / 2 * Dg f g D L x

end KarimiPL.ProxGrad


