-- Prove2me | Definitions.Def_AdamDyn_DecConv_ODEInf
-- name    : AdamDyn_DecConv_ODEInf
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T22:07:49.47778+00:00
-- url     : https://prove2.me/theorems/b97a832d-418b-4520-b991-c2aa9fe5d997
-- title:
--   Global solutions of (ODE$_\infty$) $\dot z = h_\infty(z)$ with a given initial condition, the set $Z^\infty_\infty(z_0)$
-- statement:
--   Fix $d \ge 0$, constants $a, b, \varepsilon$, a function $F : \mathbb R^d \to \mathbb R$ and a map $S : \mathbb R^d \to \mathbb R^d$. The state space is $\mathcal Z = \mathbb R^d \times \mathbb R^d \times \mathbb R^d$, a point being $z = (x, m, v)$. Let $h_\infty$ be the autonomous Adam field of (7.1),
--   $$ h_\infty(x, m, v) = \Big( -\frac{m}{\varepsilon + \sqrt{|v|}},\ a(\nabla F(x) - m),\ b(S(x) - |v|) \Big), $$
--   the first block coordinatewise, extended from $\mathcal Z_+$ to $\mathcal Z$ by $|v|$ as in the paper.
--
--   A map $z : [0, +\infty) \to \mathcal Z$ is a **global solution of** $(\mathrm{ODE}_\infty)$ $\dot z(t) = h_\infty(z(t))$ **with initial condition** $z_0$, written $z \in Z^\infty_\infty(z_0)$, if $z$ is continuous on $[0,+\infty)$, continuously differentiable on $(0,+\infty)$, satisfies $\dot z(t) = h_\infty(z(t))$ at every $t > 0$, and $z(0) = z_0$.
--
--   This is the solution notion in which Proposition 7.13 asserts existence and uniqueness from every point of $\mathcal Z_+$; $h_\infty$ is the limit of the non-autonomous Adam field as $t \to \infty$.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` and $\mathcal Z$ the product type. A solution is a map $\mathbb R \to \mathcal Z$ whose values at negative times play no role. The field $h_\infty$ is the shared definition `AdamDyn.ODEConv.adamFieldInf`.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 12 (Eq. (7.1), the |v| extension, the solution sets Z^η_T with η = T = ∞)

import Mathlib
import Definitions.Def_AdamDyn_ODEConv_AdamField
import Definitions.Def_AdamDyn_WellPosed_adamField

open scoped NNReal

namespace AdamDyn.DecConv

/-- `z ∈ Z^∞_∞(z0)` (p. 12): a global solution of `(ODE∞) ż(t) = h∞(z(t))` with initial condition
`z0`, i.e. `z` is continuous on `[0, +∞)`, continuously differentiable on `(0, +∞)`, the equation
holds at every `t > 0`, and `z(0) = z0`. Values of `z` at negative times are irrelevant. -/
def IsSolutionInf {d : ℕ} (a b ε : ℝ) (F : AdamDyn.WellPosed.Vec d → ℝ) (S : AdamDyn.WellPosed.Vec d → AdamDyn.WellPosed.Vec d) (z0 : AdamDyn.WellPosed.State d)
    (z : ℝ → AdamDyn.WellPosed.State d) : Prop :=
  ContinuousOn z (Set.Ici 0) ∧ ContDiffOn ℝ 1 z (Set.Ioi 0) ∧
    (∀ t, 0 < t → HasDerivAt z (AdamDyn.ODEConv.adamFieldInf a b ε F S (z t)) t) ∧ z 0 = z0

end AdamDyn.DecConv


