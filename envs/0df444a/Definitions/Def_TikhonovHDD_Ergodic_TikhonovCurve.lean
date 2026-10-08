-- Prove2me | Definitions.Def_TikhonovHDD_Ergodic_TikhonovCurve
-- name    : TikhonovHDD_Ergodic_TikhonovCurve
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:23:43.337575+00:00
-- url     : https://prove2.me/theorems/b267d5e4-7038-46e4-91a5-f75ec2b9b4c5
-- title:
--   argmin g, its minimum-norm element x*, and the Tikhonov approximation curve x_ε (p. 18)
-- statement:
--   Let $\mathcal H$ be a real inner product space and $g:\mathcal H\to\mathbb R$. This file fixes three objects of §4 of the paper.
--
--   1. **The solution set.** $\operatorname{argmin} g=\{x\in\mathcal H:\ g(x)\le g(y)\text{ for every }y\in\mathcal H\}$.
--   2. **The minimum-norm minimizer.** A point $x^*$ is *the element of minimum norm* of $\operatorname{argmin} g$ if
--   $$
--   x^*\in\operatorname{argmin} g\quad\text{and}\quad \|x^*\|\le\|z\|\ \text{ for every } z\in\operatorname{argmin} g,
--   $$
--   that is, $x^*=\operatorname{argmin}\{\|x\|: x\in\operatorname{argmin} g\}$.
--   3. **Points of the Tikhonov approximation curve.** For $\epsilon\in\mathbb R$, a point $y$ is a *Tikhonov point* $x_\epsilon$ if it minimizes the regularized function over the whole space:
--   $$
--   g(y)+\frac{\epsilon}{2}\|y\|^2\le g(z)+\frac{\epsilon}{2}\|z\|^2\quad\text{for every } z\in\mathcal H .
--   $$
--
--   When $\operatorname{argmin} g$ is nonempty, closed and convex in a Hilbert space (as it is for a continuous convex $g$), the minimum-norm element exists and is unique; for convex $g$ and $\epsilon>0$ the regularized function is strongly convex, so a Tikhonov point is unique when it exists. These objects carry the strong-convergence results of the paper: the trajectories of the regularized dynamics are compared with the curve $\epsilon\mapsto x_\epsilon$, whose limit as $\epsilon\to0$ is $x^*$.
--
--   **Formalization Note** Both $x^*$ and $x_\epsilon$ are encoded as predicates on a candidate point rather than as chosen values, so no statement depends on an unproved existence claim. Statements that need the whole curve take a selection $\epsilon\mapsto x_\epsilon$ satisfying the predicate for every $\epsilon>0$.
-- source:
--   Boţ, Csetnek, László, Tikhonov regularization of a second order dynamical system with Hessian driven damping, arXiv:1911.12845v2, p. 18, §4 (definition of xϵ and of x∗ = argmin{‖x‖ : x ∈ argmin g})

import Mathlib
import Definitions.Def_TikhonovHDD_Strong_Setting

namespace TikhonovHDD.Ergodic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `y` is a point `x_e` of the Tikhonov approximation curve (p. 18): it minimizes the
regularized function `g + (e/2)‖·‖²` over all of `H`. -/
def IsTikhonovPoint (g : H → ℝ) (e : ℝ) (y : H) : Prop :=
  ∀ z, g y + e / 2 * ‖y‖ ^ 2 ≤ g z + e / 2 * ‖z‖ ^ 2

end TikhonovHDD.Ergodic


