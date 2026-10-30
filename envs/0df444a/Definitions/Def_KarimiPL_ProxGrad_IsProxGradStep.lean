-- Prove2me | Definitions.Def_KarimiPL_ProxGrad_IsProxGradStep
-- name    : KarimiPL_ProxGrad_IsProxGradStep
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:55:00.853843+00:00
-- url     : https://prove2.me/theorems/65fcfa34-73ad-4df4-9f90-93a4204e80ff
-- title:
--   Proximal-gradient step: minimizer of the bracket in $\mathcal D_g(x,\alpha)$
-- statement:
--   Throughout, $\mathbb{R}^d$ carries the Euclidean inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$. The composite objective is $F = f + g$, where $f : \mathbb{R}^d \to \mathbb{R}$ is differentiable and $g : \mathbb{R}^d \to (-\infty, +\infty]$ is extended-valued with effective domain $D = \{x : g(x) < +\infty\}$.
--
--   Let $\alpha \in \mathbb{R}$ and $x \in \mathbb{R}^d$. A point $p$ is a **proximal-gradient step from $x$ with parameter $\alpha$** if $p$ attains the minimum
--   $$p \in \operatorname*{argmin}_{y \in \mathbb{R}^d} \Big[ \langle \nabla f(x), y - x\rangle + \frac{\alpha}{2}\|y - x\|^2 + g(y) - g(x) \Big],$$
--   that is, $p \in D$ and the bracket at $p$ is at most the bracket at every $y \in D$ (the bracket is $+\infty$ off $D$).
--
--   With $\alpha = L$ this is the update $x_{k+1}$ of the proximal-gradient method with step size $1/L$, eq. (14) of Karimi, Nutini and Schmidt; the same bracket defines the quantity $\mathcal D_g(x,\alpha)$ of eq. (13).
--
--   **Formalization Note** The extended-valued $g$ is given by the set $D$ and real values $g : \mathbb{R}^d \to \mathbb{R}$; values off $D$ are never used. The argmin is a predicate: neither existence of a minimizer nor closedness or lower semicontinuity of $g$ is assumed. When $\alpha > 0$ and $g$ is convex the bracket is strongly convex in $y$, so the minimizer is unique when it exists.
-- source:
--   Karimi, Nutini, Schmidt, Linear Convergence of Gradient and Proximal-Gradient Methods Under the Polyak-Łojasiewicz Condition, arXiv:1608.04636v4, §4, eq. (13) and (14), p. 8

import Mathlib

open scoped InnerProductSpace

namespace KarimiPL.ProxGrad

/-- **Proximal-gradient step: `p` attains the minimum in (13) at `x`; with `α = L` this is the
update (14).**
Karimi, Nutini, Schmidt, *Linear Convergence of Gradient and Proximal-Gradient Methods Under the
Polyak-Łojasiewicz Condition*, arXiv:1608.04636v4, eq. (13) and (14), p. 8:
"Dg(x, α) ≡ −2α min_y [⟨∇f(x), y − x⟩ + (α/2)||y − x||² + g(y) − g(x)]" and
"xk+1 = argmin_y [⟨∇f(xk), y − xk⟩ + (L/2)||y − xk||² + g(y) − g(xk)]".

`IsProxGradStep f g D α x p` says: `p ∈ D`, and for every `y ∈ D`
`⟨∇f(x), p − x⟩ + (α/2)‖p − x‖² + g(p) − g(x) ≤ ⟨∇f(x), y − x⟩ + (α/2)‖y − x‖² + g(y) − g(x)`.

**Formalization Note.** The paper's `g : ℝᵈ → (−∞, ∞]` (§4, p. 8: e.g. indicator functions of
convex sets) is encoded by its effective domain `D` and its finite values `g : ℝᵈ → ℝ` on `D`;
values of `g` off `D` are never used here. Points `y ∉ D` have objective `+∞`, so the minimum
ranges over `y ∈ D`. The argmin is a predicate, not a function: neither existence of a minimizer
nor closedness or lower semicontinuity of `g` is assumed. For `α > 0` the objective is strongly
convex in `y` when `g` is convex, so a minimizer is unique when it exists. The constant `− g(x)`
of the paper's bracket is kept. `ℝᵈ` is `EuclideanSpace ℝ (Fin d)` and `∇` is Mathlib's
`gradient`. -/
def IsProxGradStep {d : ℕ} (f g : EuclideanSpace ℝ (Fin d) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin d))) (α : ℝ) (x p : EuclideanSpace ℝ (Fin d)) : Prop :=
  p ∈ D ∧ ∀ y ∈ D,
    ⟪gradient f x, p - x⟫_ℝ + α / 2 * ‖p - x‖ ^ 2 + g p - g x ≤
      ⟪gradient f x, y - x⟫_ℝ + α / 2 * ‖y - x‖ ^ 2 + g y - g x

end KarimiPL.ProxGrad


