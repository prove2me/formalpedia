-- Prove2me | Definitions.Def_ResetInventory_A3
-- name    : ResetInventory_A3
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:20:30.255778+00:00
-- url     : https://prove2.me/theorems/d4b5bea2-13ed-417f-9cb6-b76b92e6ed93
-- title:
--   Assumption 3: concave non-decreasing reset cost $R(\cdot,t)$
-- statement:
--   **Assumption 3 at age $t$.** The known initial state is $\zeta=0$, and the expected reset cost $R(x,t)=\mathbb E\,s(x,t,w)$ satisfies the following on $[0,c_{\max}]$.
--
--   1. $R(\cdot,t)$ is concave and non-decreasing.
--   2. It is differentiable, with $|\partial_xR(x,t)|\le\eta_t$.
--   3. Its derivative is Lipschitz:
--   $$
--   |\partial_xR(x,t)-\partial_xR(x',t)|\le L_t\,|x-x'| .
--   $$
--
--   Here $\eta_t,L_t\ge0$. Concavity of the reset cost against convexity of the no-reset cost is what cuts the reset region into two end intervals.
--
--   **Formalization Note** The derivative is taken within $[0,c_{\max}]$ (one-sided at the ends) and named explicitly; $L_t$ is written `Lt t`. The state $\zeta=0$ is built into the order value after a reset. The range of $t$ is imposed where A3 is used: Theorem 1 uses it for $t=0,\dots,k$.
-- source:
--   Lee, Mintz, Aswani, Shen, Yang, Optimal Policy for Inventory Management with Periodic and Controlled Resets, arXiv:2209.03571v1, Assumption 3, (25), p.16

import Mathlib
import Definitions.Def_ResetInventory_ResetModel

namespace ResetInventory

/-- **Assumption 3 (A3)** at the age `t` (Lee, Mintz, Aswani, Shen, Yang, arXiv:2209.03571v1,
p.16): the expected reset cost `R(·, t)` is concave and non-decreasing in `x`, and its derivative
`∂ₓR(·, t)` satisfies `|∂ₓR(x, t)| ≤ η_t` and `|∂ₓR(x, t) − ∂ₓR(x', t)| ≤ L_t |x − x'|` (25), with
`η_t, L_t ≥ 0`. (The known initial state `ζ = 0` of A3 is built into `orderValue`.)

**Formalization Note** Everything is on the state domain `[0, c_max]`, with the derivative taken
within `[0, c_max]` (one-sided at the ends) and named explicitly (`R'`). The constant `L_t` is
called `Lt t`. The paper states A3 for `t = 0, …, k − 1`; the range is imposed where A3 is used
(Theorem 1 uses it for `t = 0, …, k`, see there). -/
def A3 (mdl : ResetModel) (η Lt : ℕ → ℝ) (t : ℕ) : Prop :=
  0 ≤ η t ∧ 0 ≤ Lt t ∧
  ConcaveOn ℝ (Set.Icc 0 mdl.cmax) (fun x => mdl.R x t) ∧
  MonotoneOn (fun x => mdl.R x t) (Set.Icc 0 mdl.cmax) ∧
  ∃ R' : ℝ → ℝ, ∀ x ∈ Set.Icc 0 mdl.cmax,
    HasDerivWithinAt (fun y => mdl.R y t) (R' x) (Set.Icc 0 mdl.cmax) x ∧
    |R' x| ≤ η t ∧
    ∀ y ∈ Set.Icc 0 mdl.cmax, |R' x - R' y| ≤ Lt t * |x - y|

end ResetInventory


