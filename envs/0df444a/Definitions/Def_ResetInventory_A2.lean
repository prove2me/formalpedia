-- Prove2me | Definitions.Def_ResetInventory_A2
-- name    : ResetInventory_A2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:20:32.558991+00:00
-- url     : https://prove2.me/theorems/05d8aaf9-6620-42fa-a11d-c74aef10ce92
-- title:
--   Assumption 2: strongly convex stage cost $H(\cdot,t)$
-- statement:
--   **Assumption 2 at age $t$.** The function $H(\cdot,t)$ of the expected stage cost $\mathbb E\,g=c\,u+K\cdot\mathbf 1_{\mathbb R^*_+}(u)+H(\xi+u,\tau)$ (24) is twice differentiable on $[0,c_{\max}]$, and for every $z\in[0,c_{\max}]$
--   $$
--   |\partial_xH(z,t)|\le\kappa_t,\qquad \partial_{xx}H(z,t)\ge m_t,
--   $$
--   with constants $\kappa_t\ge0$ and $m_t>0$.
--
--   The lower bound $m_t>0$ makes $H(\cdot,t)$ strongly convex, which is what keeps the no-reset cost convex once the discount factor is small.
--
--   **Formalization Note** The derivatives are taken in the first argument, within $[0,c_{\max}]$ (one-sided at $0$ and $c_{\max}$), at every post-order stock $z=x+u\in[0,c_{\max}]$, and are named explicitly. The paper's retail example has $\partial_{xx}H=(p+q)f$, with a jump of $f$ at $0$, which is why the derivatives are one-sided at the ends. The range $t=0,\dots,k-1$ and the conditions $c,K\ge0$ are imposed where A2 is used.
-- source:
--   Lee, Mintz, Aswani, Shen, Yang, Optimal Policy for Inventory Management with Periodic and Controlled Resets, arXiv:2209.03571v1, Assumption 2, (24), p.15

import Mathlib
import Definitions.Def_ResetInventory_ResetModel

namespace ResetInventory

/-- **Assumption 2 (A2)** at the age `t` (Lee, Mintz, Aswani, Shen, Yang, arXiv:2209.03571v1,
p.15): the function `H(·, t)` of the expected stage cost (24) satisfies `|∂ₓH(z, t)| ≤ κ_t` and
`∂ₓₓH(z, t) ≥ m_t`, with `κ_t ≥ 0` and `m_t > 0`.

**Formalization Note** The derivatives are taken with respect to the first argument, within the
state domain `[0, c_max]` (one-sided at `0` and `c_max`), at every post-order stock
`z = x + u ∈ [0, c_max]`; the first and second derivatives are named explicitly (`H'`, `H''`), so
no junk value of `deriv` can enter. The paper's retail example has `∂ₓₓH = (p + q) f` with a jump
of `f` at `0`, which is why the derivatives are one-sided at the ends. The paper states A2 for
`t = 0, …, k − 1`; that range is imposed where A2 is used. The conditions `c, K ≥ 0` of A2 are
separate hypotheses of the theorems. -/
def A2 (mdl : ResetModel) (κ m : ℕ → ℝ) (t : ℕ) : Prop :=
  0 ≤ κ t ∧ 0 < m t ∧
  ∃ H' H'' : ℝ → ℝ, ∀ z ∈ Set.Icc 0 mdl.cmax,
    HasDerivWithinAt (fun y => mdl.H y t) (H' z) (Set.Icc 0 mdl.cmax) z ∧
    HasDerivWithinAt H' (H'' z) (Set.Icc 0 mdl.cmax) z ∧
    |H' z| ≤ κ t ∧ m t ≤ H'' z

end ResetInventory


