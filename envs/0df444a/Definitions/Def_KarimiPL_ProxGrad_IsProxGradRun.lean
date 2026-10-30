-- Prove2me | Definitions.Def_KarimiPL_ProxGrad_IsProxGradRun
-- name    : KarimiPL_ProxGrad_IsProxGradRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:56:17.207257+00:00
-- url     : https://prove2.me/theorems/e053a3b6-7c44-48ea-b446-7e7068d2023d
-- title:
--   A run of the proximal-gradient method with step size $1/L$
-- statement:
--   Throughout, $\mathbb{R}^d$ carries the Euclidean inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$. The composite objective is $F = f + g$, where $f : \mathbb{R}^d \to \mathbb{R}$ is differentiable and $g : \mathbb{R}^d \to (-\infty, +\infty]$ is extended-valued with effective domain $D = \{x : g(x) < +\infty\}$.
--
--   Let $L \in \mathbb{R}$. A sequence $(x_k)_{k \ge 0}$ in $\mathbb{R}^d$ is a **run of the proximal-gradient method with step size $1/L$** if for every $k \ge 0$
--   $$x_{k+1} \in \operatorname*{argmin}_{y} \Big[ \langle \nabla f(x_k), y - x_k\rangle + \frac{L}{2}\|y - x_k\|^2 + g(y) - g(x_k) \Big],$$
--   which is the update (14) of Karimi, Nutini and Schmidt.
--
--   **Formalization Note** Each step is the predicate "proximal-gradient step from $x_k$ with parameter $L$" (a minimizer over $D$), so the existence of every iterate is part of the hypothesis and no closedness of $g$ is assumed. The initial point $x_0$ is unconstrained here; the theorems require $x_0 \in D$.
-- source:
--   Karimi, Nutini, Schmidt, Linear Convergence of Gradient and Proximal-Gradient Methods Under the Polyak-Łojasiewicz Condition, arXiv:1608.04636v4, Theorem 5, eq. (14), p. 8

import Mathlib
import Definitions.Def_KarimiPL_ProxGrad_IsProxGradStep

namespace KarimiPL.ProxGrad

/-- **A run of the proximal-gradient method (14) with step size `1/L`.**
Karimi, Nutini, Schmidt, *Linear Convergence of Gradient and Proximal-Gradient Methods Under the
Polyak-Łojasiewicz Condition*, arXiv:1608.04636v4, Theorem 5, eq. (14), p. 8: "the
proximal-gradient method with a step-size of 1/L,
xk+1 = argmin_y [⟨∇f(xk), y − xk⟩ + (L/2)||y − xk||² + g(y) − g(xk)] (14)".

`IsProxGradRun f g D L x` says: for every `k`, `x (k+1)` is a minimizer of the bracket of (14)
at `x k`, i.e. `IsProxGradStep f g D L (x k) (x (k+1))`.

**Formalization Note.** The argmin is a minimizer predicate (see `IsProxGradStep`); the run
hypothesis carries the existence of every prox point, so no closedness of `g` is needed. The
same `L` is the constant of (2), the step `1/L` and the `α` of `Dg(·, L)` in (12). The initial
point `x 0` is free; the theorems add `x 0 ∈ D`. -/
def IsProxGradRun {d : ℕ} (f g : EuclideanSpace ℝ (Fin d) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin d))) (L : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ k : ℕ, IsProxGradStep f g D L (x k) (x (k + 1))

end KarimiPL.ProxGrad


