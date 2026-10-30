-- Prove2me | Definitions.Def_KarimiPL_ProxGrad_Dg
-- name    : KarimiPL_ProxGrad_Dg
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:55:19.495762+00:00
-- url     : https://prove2.me/theorems/cb8216bc-f552-4e1b-86b6-c1ea3b0606cb
-- title:
--   The quantity $\mathcal D_g(x,\alpha)$ of the proximal-PL inequality
-- statement:
--   Throughout, $\mathbb{R}^d$ carries the Euclidean inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$. The composite objective is $F = f + g$, where $f : \mathbb{R}^d \to \mathbb{R}$ is differentiable and $g : \mathbb{R}^d \to (-\infty, +\infty]$ is extended-valued with effective domain $D = \{x : g(x) < +\infty\}$.
--
--   For $\alpha \in \mathbb{R}$ and $x \in \mathbb{R}^d$ define
--   $$\mathcal D_g(x,\alpha) = -2\alpha \min_{y \in \mathbb{R}^d} \Big[ \langle \nabla f(x), y - x\rangle + \frac{\alpha}{2}\|y - x\|^2 + g(y) - g(x) \Big].$$
--   Since the bracket is $+\infty$ off $D$, the minimum is taken over $y \in D$. For $g \equiv 0$ and $\alpha > 0$ one gets $\mathcal D_g(x,\alpha) = \|\nabla f(x)\|^2$, so the proximal-PL inequality built on $\mathcal D_g$ reduces to the PL inequality.
--
--   **Formalization Note** Lean takes the real infimum over $y \in D$ in place of the minimum. It equals the paper's minimum whenever a minimizer exists, and the mission only evaluates $\mathcal D_g$ at such points. Where no minimizer exists the paper's expression is undefined and Lean's infimum takes the junk value $0$ (for $D = \emptyset$ or a bracket unbounded below).
-- source:
--   Karimi, Nutini, Schmidt, Linear Convergence of Gradient and Proximal-Gradient Methods Under the Polyak-Łojasiewicz Condition, arXiv:1608.04636v4, §4, eq. (13), p. 8

import Mathlib

open scoped InnerProductSpace

namespace KarimiPL.ProxGrad

/-- **The quantity `Dg(x, α)` of (13).**
Karimi, Nutini, Schmidt, *Linear Convergence of Gradient and Proximal-Gradient Methods Under the
Polyak-Łojasiewicz Condition*, arXiv:1608.04636v4, eq. (13), p. 8:
"Dg(x, α) ≡ −2α min_y [⟨∇f(x), y − x⟩ + (α/2)||y − x||² + g(y) − g(x)]".

`Dg f g D α x = −2α · inf_{y ∈ D} (⟨∇f(x), y − x⟩ + (α/2)‖y − x‖² + g(y) − g(x))`.

**Formalization Note.** The paper's extended-valued `g` is encoded by its effective domain `D`
and its finite values `g` on `D`; off `D` the bracket is `+∞`, so the minimum over `y ∈ ℝᵈ` is
the minimum over `y ∈ D`. The paper writes `min`; Lean's real infimum `⨅` is used instead. It
equals the paper's minimum whenever a minimizer exists (that is, whenever
`IsProxGradStep f g D α x p` holds for some `p`), and this mission only uses `Dg` at such
points. Where no minimizer exists the paper's `min` is undefined and Lean's `⨅` takes a junk
value: `0` when `D = ∅` or when the bracket is unbounded below on `D`. `ℝᵈ` is
`EuclideanSpace ℝ (Fin d)` and `∇` is Mathlib's `gradient`. -/
noncomputable def Dg {d : ℕ} (f g : EuclideanSpace ℝ (Fin d) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin d))) (α : ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  -2 * α * ⨅ y : D,
    (⟪gradient f x, (y : EuclideanSpace ℝ (Fin d)) - x⟫_ℝ +
      α / 2 * ‖(y : EuclideanSpace ℝ (Fin d)) - x‖ ^ 2 + g y - g x)

end KarimiPL.ProxGrad


