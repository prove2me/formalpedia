-- Prove2me | Definitions.Def_ResetInventory_Mbound
-- name    : ResetInventory_Mbound
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:20:39.919327+00:00
-- url     : https://prove2.me/theorems/ed981c01-ed30-43c7-9fbb-999a26f5b9da
-- title:
--   The derivative bound $M_t$
-- statement:
--   The **derivative bound** of Proposition 6 at age $t$ is
--   $$
--   M_t=\eta_t+c+\kappa_t+\frac{m_t}{L\,c_{\max}+P},
--   $$
--   where $\kappa_t,m_t$ are the constants of Assumption 2, $\eta_t$ that of Assumption 3, $c$ the unit ordering cost, and $L,P$ the Lipschitz constant and the bound of the demand density (Assumption 5). It bounds the derivative of every piece of the value function $J(\cdot,t)$, and it is the constant that restarts the backward induction of Theorem 1.
--
--   **Formalization Note** Under Assumption 5 the denominator is positive: a probability density that vanishes on $(-\infty,0)$ and is bounded by $P$ on $[0,\infty)$ forces $P>0$.
-- source:
--   Lee, Mintz, Aswani, Shen, Yang, Optimal Policy for Inventory Management with Periodic and Controlled Resets, arXiv:2209.03571v1, Proposition 6, p.21

import Mathlib
import Definitions.Def_ResetInventory_ResetModel

namespace ResetInventory

/-- The derivative bound `M_t = η_t + c + κ_t + m_t / (L c_max + P)` of Proposition 6 (Lee, Mintz,
Aswani, Shen, Yang, arXiv:2209.03571v1, p.21), where `κ_t, m_t` are the constants of Assumption 2,
`η_t` that of Assumption 3, and `L, P` the Lipschitz constant and the bound of the demand density
(Assumption 5).

**Formalization Note** The division is never by zero under Assumption 5: a probability density
bounded by `P` on `[0, ∞)` and vanishing on `(-∞, 0)` forces `P > 0`, so `L c_max + P > 0`. -/
noncomputable def Mbound (mdl : ResetModel) (κ m η : ℕ → ℝ) (L P : ℝ) (t : ℕ) : ℝ :=
  η t + mdl.c + κ t + m t / (L * mdl.cmax + P)

end ResetInventory


