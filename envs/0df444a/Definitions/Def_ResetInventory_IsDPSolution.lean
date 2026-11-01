-- Prove2me | Definitions.Def_ResetInventory_IsDPSolution
-- name    : ResetInventory_IsDPSolution
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:21:32.231125+00:00
-- url     : https://prove2.me/theorems/ab7365dc-377a-4aaa-a58a-598271d7a1e5
-- title:
--   Solution of the dynamic programming equations (22)
-- statement:
--   A function $J(x,t)$ **solves the dynamic programming equations (22)** if, with $J_0=J(\zeta,0)=J(0,0)$, $R(x,t)=\mathbb E\,s(x,t,w)$ and $\mathcal U_t(x)=[0,c_{\max}-x]$:
--
--   1. $J_0=\min_{u\in[0,c_{\max}]}Q_J(0,0,u)$;
--   2. for every $x\in[0,c_{\max}]$ and $t=0,\dots,k-1$,
--   $$
--   J(x,t)=\min\Big\{J_0+R(x,t),\ \min_{u\in\mathcal U_t(x)}Q_J(x,t,u)\Big\};
--   $$
--   3. $J(x,k)=J_0+R(x,k)$ for every $x\in[0,c_{\max}]$.
--
--   Here $Q_J(x,t,u)=c\,u+K\mathbf 1_{\mathbb R^*_+}(u)+H(x+u,t)+\gamma\,\mathbb E J((x+u-w)^+,t+1)$. The first term of the outer minimum is the value of resetting (discard the stock at cost $R(x,t)$, then continue from $(\zeta,0)$); the second is the value of keeping the stock and ordering $u$. At age $k$ a reset is forced.
--
--   **Formalization Note** Each inner minimum is stated as attained: the minimum exists and some feasible order achieves it, as the paper's $\min$ asserts. The state domain is $[0,c_{\max}]$. Proposition 1, which derives (22) from the stochastic control problem (2), is cited by the paper from Mintz et al. (2017) and is not formalized: in this mission "optimal" means attaining the minima in (22).
-- source:
--   Lee, Mintz, Aswani, Shen, Yang, Optimal Policy for Inventory Management with Periodic and Controlled Resets, arXiv:2209.03571v1, (22), Proposition 1, p.14; J₀, p.13; Assumption 4, p.16

import Mathlib
import Definitions.Def_ResetInventory_orderValue

namespace ResetInventory

/-- `J` solves the dynamic programming equations (22) of Proposition 1 (Lee, Mintz, Aswani, Shen,
Yang, arXiv:2209.03571v1, p.14) on the state domain `[0, c_max] × {0, …, k}`:

* `J(ζ, 0) = min_{u ∈ U₀} E[g(ζ, 0, u, w) + γ J(h(ζ, 0, u, w), 1)]`, with `ζ = 0`;
* `J(x, t) = min{ J₀ + E(s(x, t, w)), min_{u ∈ U_t} E[g(x, t, u, w) + γ J(h(x, t, u, w), t + 1)] }`
  for every `x ∈ [0, c_max]` and `t = 0, …, k − 1`;
* `J(x, k) = J₀ + E(s(x, k, w))` for every `x ∈ [0, c_max]`,

where `J₀ = J(ζ, 0) = J(0, 0)` (p.13), `E s(x, t, w) = R(x, t)`, the inner expectation is
`orderValue`, and `U_t = {u : 0 ≤ u ≤ c_max − x}` (Assumption 4).

**Formalization Note** Each inner minimum is stated as `IsLeast` of the set of values over the
feasible orders: the minimum exists and is attained, as the paper's `min` asserts. The state
domain is `[0, c_max]` (the domain of Assumption T, p.17; from a state in `[0, c_max]` the dynamics
stay there, and for `x > c_max` there is no feasible order). Proposition 1, which links (22) to the
stochastic control problem (2), is cited by the paper from Mintz et al. (2017) and is not
formalized; "optimal" in this mission means attaining the minima in (22). -/
def IsDPSolution (mdl : ResetModel) (J : ℝ → ℕ → ℝ) : Prop :=
  IsLeast (orderValue mdl J 0 0 '' Set.Icc 0 mdl.cmax) (J 0 0) ∧
  (∀ x ∈ Set.Icc 0 mdl.cmax, ∀ t < mdl.k, ∃ v : ℝ,
    IsLeast (orderValue mdl J x t '' Set.Icc 0 (mdl.cmax - x)) v ∧
    J x t = min (J 0 0 + mdl.R x t) v) ∧
  (∀ x ∈ Set.Icc 0 mdl.cmax, J x mdl.k = J 0 0 + mdl.R x mdl.k)

end ResetInventory


