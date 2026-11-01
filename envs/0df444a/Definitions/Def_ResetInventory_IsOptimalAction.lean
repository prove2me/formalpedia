-- Prove2me | Definitions.Def_ResetInventory_IsOptimalAction
-- name    : ResetInventory_IsOptimalAction
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:21:33.6868+00:00
-- url     : https://prove2.me/theorems/c2040df8-d862-4bf2-b948-520c59197559
-- title:
--   An action attains the minimum in (22)
-- statement:
--   Let $J$ be a cost-to-go. An action $(r,u)$ at the state $(x,t)$ **attains the minimum in (22)** if it is feasible and its value equals $J(x,t)$:
--
--   1. a reset ($r=1$): $u\in[0,c_{\max}]$ and $J(x,t)=R(x,t)+Q_J(0,0,u)$. The system is reset to $(\zeta,0)=(0,0)$ at cost $R(x,t)$, then orders $u$;
--   2. no reset ($r=0$): $u\in[0,c_{\max}-x]$ and $J(x,t)=Q_J(x,t,u)$.
--
--   Here $Q_J(x,t,u)=c\,u+K\mathbf 1_{\mathbb R^*_+}(u)+H(x+u,t)+\gamma\,\mathbb E J((x+u-w)^+,t+1)$.
--
--   When $J$ solves (22), $J(x,t)$ is the minimum over all feasible actions, so this says that $(r,u)$ is a minimizer, i.e. an optimal action.
--
--   **Formalization Note** This is the mission's reading of "optimal": attainment of the minima in (22). Proposition 1, which links (22) to the stochastic control problem (2), is not formalized. For a reset the order $u$ must itself attain $J_0=J(0,0)$.
-- source:
--   Lee, Mintz, Aswani, Shen, Yang, Optimal Policy for Inventory Management with Periodic and Controlled Resets, arXiv:2209.03571v1, (22), p.14; Proposition 5, p.19

import Mathlib
import Definitions.Def_ResetInventory_orderValue

namespace ResetInventory

/-- The action `a = (r, u)` attains the minimum of the dynamic programming equation (22) at the
state `(x, t)` (Lee, Mintz, Aswani, Shen, Yang, arXiv:2209.03571v1, p.14): the action is feasible
and its value equals `J(x, t)`.

* A reset (`r = 1`) moves the system to `(ζ, 0) = (0, 0)` at the cost `R(x, t) = E s(x, t, w)`
  and then orders `u ∈ [0, c_max]`; its value is `R(x, t) + E[g(ζ, 0, u, w) + γ J(h(ζ, 0, u, w), 1)]`.
* No reset (`r = 0`) orders `u ∈ [0, c_max − x]` (Assumption 4); its value is
  `E[g(x, t, u, w) + γ J(h(x, t, u, w), t + 1)]`.

**Formalization Note** When `J` solves (22) (`IsDPSolution`), `J(x, t)` is the minimum over all
feasible actions, so "the value of `a` equals `J(x, t)`" says that `a` is a minimizer: this is the
mission's reading of "optimal" (Proposition 1 is not formalized). For a reset the order `u` must
itself attain `J₀ = J(0, 0)` for the value to equal `J₀ + R(x, t)`. -/
def IsOptimalAction (mdl : ResetModel) (J : ℝ → ℕ → ℝ) (x : ℝ) (t : ℕ) (a : Bool × ℝ) : Prop :=
  if a.1 then
    a.2 ∈ Set.Icc 0 mdl.cmax ∧ J x t = mdl.R x t + orderValue mdl J 0 0 a.2
  else
    a.2 ∈ Set.Icc 0 (mdl.cmax - x) ∧ J x t = orderValue mdl J x t a.2

end ResetInventory


