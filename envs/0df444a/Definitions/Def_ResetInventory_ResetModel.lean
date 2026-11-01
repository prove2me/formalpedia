-- Prove2me | Definitions.Def_ResetInventory_ResetModel
-- name    : ResetInventory_ResetModel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:19:40.195888+00:00
-- url     : https://prove2.me/theorems/9f11952f-0c2a-45d7-a82c-7bcad9978676
-- title:
--   Data of the inventory problem with periodic and controlled resets
-- statement:
--   The **reset inventory model** is given by the following data.
--
--   1. A horizon $k\in\mathbb N$: the stock may age at most $k$ periods between two resets ($t_n\le k$).
--   2. A capacity $c_{\max}$: after ordering, the stock never exceeds $c_{\max}$.
--   3. A unit ordering cost $c$ and a fixed ordering cost $K$.
--   4. A discount factor $\gamma$.
--   5. For each age $t$, a function $H(\cdot,t)$ such that the expected stage cost of ordering $u$ at the pseudo-state $(\xi,\tau)$ is
--   $$
--   \mathbb E\,g(\xi,\tau,u,w)=c\,u+K\cdot\mathbf 1_{\mathbb R^*_+}(u)+H(\xi+u,\tau),\qquad \mathbf 1_{\mathbb R^*_+}(u)=\begin{cases}1,&u>0,\\0,&\text{otherwise.}\end{cases}
--   $$
--   6. The expected reset cost $R(x,t)=\mathbb E\,s(x,t,w)$ of discarding the stock $x$ at age $t$.
--   7. The density $f$ of the i.i.d. demands $w_n$.
--
--   The stock evolves as $x_{n+1}=(\xi_n+u_n-w_n)^+$, and a reset returns the system to the known state $(\zeta,0)=(0,0)$.
--
--   This structure carries everything the dynamic programming equations (22) need. The assumptions A2, A3 and A5 are separate predicates on it.
--
--   **Formalization Note** The stage cost $g$ and the reset cost $s$ enter the dynamic programming equations only through $\mathbb E g$ and $\mathbb E s$, so the model stores $c,K,H,R$ instead of $g$ and $s$. The structure imposes no condition by itself.
-- source:
--   Lee, Mintz, Aswani, Shen, Yang, Optimal Policy for Inventory Management with Periodic and Controlled Resets, arXiv:2209.03571v1, §2, (1)–(2), p.8; (21), p.13; Assumptions 1–5, pp.15–16

import Mathlib

namespace ResetInventory

/-- The data of the inventory problem with periodic and controlled resets (Lee, Mintz, Aswani,
Shen, Yang, arXiv:2209.03571v1, §2, (1)–(2), p.8, and §3.1, Assumptions 1–5, pp.15–16).

* `k` — the maximal number of periods between resets (`t_n ≤ k`, (2));
* `cmax` — the storage capacity `c_max` (Assumption 4);
* `c`, `K` — the unit and the fixed ordering cost (Assumption 2, (24));
* `γ` — the discount factor;
* `H t` — the function `H(·, t)` of the expected stage cost
  `E g(ξ, τ, u, w) = c u + K·1_{ℝ*₊}(u) + H(ξ + u, τ)` (24);
* `R x t` — the expected reset cost `R(x, t) = E s(x, t, w)` (Assumption 3);
* `f` — the density of the demand `w` (Assumption 5).

**Formalization Note** The stage cost `g` and the reset cost `s` enter the dynamic programming
equations (22) only through `E g` and `E s`, so the model carries `c`, `K`, `H` and `R` instead
of `g` and `s`. The known reset state is `ζ = 0` (Assumption 3) and the dynamics are
`x_{n+1} = (ξ_n + u_n − w_n)⁺` (Assumption 1); both are built into `orderValue`. No condition is
imposed by the structure itself; the assumptions are separate predicates. -/
structure ResetModel where
  /-- the maximal age `k` of the stock -/
  k : ℕ
  /-- the capacity `c_max` -/
  cmax : ℝ
  /-- the unit ordering cost `c` -/
  c : ℝ
  /-- the fixed ordering cost `K` -/
  K : ℝ
  /-- the discount factor `γ` -/
  γ : ℝ
  /-- `H z t = H(z, t)`, the stage-cost function of (24) -/
  H : ℝ → ℕ → ℝ
  /-- `R x t = R(x, t) = E s(x, t, w)`, the expected reset cost -/
  R : ℝ → ℕ → ℝ
  /-- the demand density `f` -/
  f : ℝ → ℝ

end ResetInventory


