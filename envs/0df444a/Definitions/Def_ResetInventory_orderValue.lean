-- Prove2me | Definitions.Def_ResetInventory_orderValue
-- name    : ResetInventory_orderValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:20:44.983737+00:00
-- url     : https://prove2.me/theorems/8966178b-ba02-4186-8ccf-06aacad147ea
-- title:
--   Value of ordering $u$ without reset at the state $(x,t)$
-- statement:
--   Given a cost-to-go $J$, the value of **not resetting and ordering $u$** at the state $(x,t)$ is
--   $$
--   Q_J(x,t,u)=c\,u+K\cdot\mathbf 1_{\mathbb R^*_+}(u)+H(x+u,t)+\gamma\,\mathbb E\,J\big((x+u-w)^+,t+1\big).
--   $$
--   This is the expression $\mathbb E\big[g(x,t,u,w)+\gamma J(h(x,t,u,w),t+1)\big]$ minimized in the dynamic programming equations (22), under the dynamics $h=(\xi+u-w)^+$ of Assumption 1 and the cost decomposition (24) of Assumption 2. At $(x,t)=(\zeta,0)=(0,0)$ it is the value of the order placed right after a reset.
--
--   **Formalization Note** The feasible orders $0\le u\le c_{\max}-x$ (Assumption 4) are imposed where this value is minimized.
-- source:
--   Lee, Mintz, Aswani, Shen, Yang, Optimal Policy for Inventory Management with Periodic and Controlled Resets, arXiv:2209.03571v1, (21), p.13; (22), p.14; Assumptions 1, 2, (24), p.15; Assumption 4, p.16

import Mathlib
import Definitions.Def_ResetInventory_ResetModel
import Definitions.Def_ResetInventory_expectedNext

namespace ResetInventory

/-- The value of not resetting and ordering `u` at the state `(x, t)`, given a cost-to-go `J`
(Lee, Mintz, Aswani, Shen, Yang, arXiv:2209.03571v1, the inner expression
`E[g(x, t, u, w) + γ J(h(x, t, u, w), t + 1)]` of (22), p.14, under Assumption 1, p.15, and (24)
of Assumption 2, p.15):
`c u + K·1_{ℝ*₊}(u) + H(x + u, t) + γ E J((x + u − w)⁺, t + 1)`,
where `1_{ℝ*₊}(u) = 1` if `u > 0` and `0` otherwise ((21), p.13).

**Formalization Note** At `(x, t) = (ζ, 0) = (0, 0)` this is the expression minimized in the
first line of (22) (the order placed right after a reset, Assumption 3: `ζ = 0`). The feasible
orders `0 ≤ u ≤ c_max − x` (Assumption 4) are imposed where the value is minimized
(`IsDPSolution`). -/
noncomputable def orderValue (mdl : ResetModel) (J : ℝ → ℕ → ℝ) (x : ℝ) (t : ℕ) (u : ℝ) : ℝ :=
  mdl.c * u + mdl.K * (if 0 < u then 1 else 0) + mdl.H (x + u) t +
    mdl.γ * expectedNext mdl.f (fun y => J y (t + 1)) (x + u)

end ResetInventory


