-- Prove2me | Definitions.Def_KarimiPL_ProxCD_IsProxGradStep
-- name    : KarimiPL_ProxCD_IsProxGradStep
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:51:37.58703+00:00
-- url     : https://prove2.me/theorems/e96e9c7d-a2f6-4ddc-b68c-8810199e65e5
-- title:
--   Proximal-gradient step: minimizer of the bracket in $\mathcal D_g(x,\alpha)$
-- statement:
--   Throughout, $\mathbb{R}^d$ carries the Euclidean inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$, $e_i$ is the $i$-th unit vector, $x_i$ the $i$-th coordinate of $x$, and $\nabla_i f(x)$ the $i$-th coordinate of $\nabla f(x)$. The composite objective is $F = f + g$ with $f : \mathbb{R}^d \to \mathbb{R}$ differentiable and $g : \mathbb{R}^d \to (-\infty, +\infty]$ extended-valued.
--
--   Let $D$ be the effective domain of $g$, $\alpha \in \mathbb{R}$ and $x \in \mathbb{R}^d$. A point $p$ is a **proximal-gradient step from $x$ with parameter $\alpha$** if $p$ attains the minimum
--   $$p \in \operatorname*{argmin}_{y \in \mathbb{R}^d} \Big[ \langle \nabla f(x), y - x\rangle + \frac{\alpha}{2}\|y - x\|^2 + g(y) - g(x) \Big],$$
--   that is, $p \in D$ and the bracket at $p$ is at most the bracket at every $y \in D$ (the bracket is $+\infty$ off $D$).
--
--   The same bracket defines the quantity $\mathcal D_g(x,\alpha)$ of eq. (13) of Karimi, Nutini and Schmidt; in this mission the predicate certifies that the minimum in $\mathcal D_g(x, L)$ is attained, for the separable $g$ of §4.3.
--
--   **Formalization Note** The extended-valued $g$ is given by the set $D$ and real values $g$; values off $D$ are never used. The argmin is a predicate: neither existence of a minimizer nor closedness or lower semicontinuity of $g$ is assumed. This definition is identical to the draft `KarimiPL.ProxGrad.IsProxGradStep` of the sibling Theorem 5 mission, redeclared because that draft is unpublished.
-- source:
--   Karimi, Nutini, Schmidt, Linear Convergence of Gradient and Proximal-Gradient Methods Under the Polyak-Łojasiewicz Condition, arXiv:1608.04636v4, §4, eq. (13), p. 8

import Mathlib

open scoped InnerProductSpace

namespace KarimiPL.ProxCD

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

end KarimiPL.ProxCD


