-- Prove2me | Definitions.Def_BnBPEP_WeakCvx_IsWeakSubgrad
-- name    : BnBPEP_WeakCvx_IsWeakSubgrad
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:45:53.410993+00:00
-- url     : https://prove2.me/theorems/2e024f41-25bd-4b03-9c10-2ae6e21f9e47
-- title:
--   Subgradients of a $\rho$-weakly convex function
-- statement:
--   Let $\rho \in \mathbb R$ and let $f:\mathbb R^d\to\mathbb R$. A vector $g\in\mathbb R^d$ is called a **subgradient of $f$ at $x$ with weak-convexity modulus $\rho$** if $f$ lies above the concave quadratic minorant built from $g$ at $x$:
--   $$f(y)\ \ge\ f(x)+\langle g,\,y-x\rangle-\frac{\rho}{2}\|y-x\|^2\qquad\text{for every } y\in\mathbb R^d.$$
--
--   This is the inequality by which Das Gupta, Van Parys and Ryu characterize the subdifferential $\partial f(x)$ of a $\rho$-weakly convex function (App. 8.1). For a $\rho$-weakly convex $f$, i.e. one for which $f+\frac{\rho}{2}\|\cdot\|^2$ is convex, the set of such $g$ is exactly the Clarke (equivalently Fréchet, or limiting) subdifferential of $f$ at $x$, namely $\{u-\rho x : u\in\partial_{\mathrm{conv}}(f+\frac{\rho}{2}\|\cdot\|^2)(x)\}$. It therefore coincides with the paper's abstract subdifferential $\partial f$ for every instance the paper admits, and it is nonempty at every point. Every statement of the mission writes "$g\in\partial f(x)$" through this predicate.
--
--   **Formalization Note** The space is `EuclideanSpace ℝ (Fin d)`. The convex subdifferential of $f$ itself is deliberately not used: for a nonconvex $f$ it can be empty, which would make statements quantified over it vacuous.
-- source:
--   Das Gupta, Van Parys, Ryu, Branch-and-bound performance estimation programming, Math. Program. 204 (2024), pp. 571–572 (§2, subdifferential and weak convexity) and p. 629 (App. 8.1, first inequality)

import Mathlib

namespace BnBPEP.WeakCvx

/-- `g` is a subgradient of a `ρ`-weakly convex function `f` at `x`
(Das Gupta–Van Parys–Ryu, Math. Program. 204 (2024), App. 8.1, p. 629):
`f y ≥ f x + ⟪g, y - x⟫ - (ρ/2)‖y - x‖²` for every `y`.
For a `ρ`-weakly convex `f` this set is the Clarke = Fréchet = limiting subdifferential
`∂f(x)`, i.e. `{u - ρx | u ∈ ∂_conv (f + (ρ/2)‖·‖²)(x)}`; it is the paper's abstract `∂f(x)`
(pp. 571–572) for every instance the paper allows. -/
def IsWeakSubgrad {d : ℕ} (ρ : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x g : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ y : EuclideanSpace ℝ (Fin d), f x + inner ℝ g (y - x) - ρ / 2 * ‖y - x‖ ^ 2 ≤ f y

end BnBPEP.WeakCvx


