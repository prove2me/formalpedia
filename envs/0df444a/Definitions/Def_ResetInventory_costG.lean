-- Prove2me | Definitions.Def_ResetInventory_costG
-- name    : ResetInventory_costG
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:20:53.470684+00:00
-- url     : https://prove2.me/theorems/855f457f-6003-434e-879f-46c4851be30c
-- title:
--   The function $G(z,t)$
-- statement:
--   For a next-period cost-to-go $V=J(\cdot,t+1)$, the paper's function $G$ is
--   $$
--   G(z,t)=c\,z+H(z,t)+\gamma\,\mathbb E\big(V((z-w)^+)\big).
--   $$
--   With it, the no-reset minimum in (22) is
--   $$
--   \min_{u\in\mathcal U_t}\mathbb E\big[g(x,t,u,w)+\gamma J(h(x,t,u,w),t+1)\big]=\min_{z\in[x,c_{\max}]}G(z,t)+K\cdot\mathbf 1_{\mathbb R^*_+}(z-x)-c\,x ,
--   $$
--   so the no-reset problem is a fixed-cost problem in the post-order level $z$, the setting of the $(s,S)$ analysis.
-- source:
--   Lee, Mintz, Aswani, Shen, Yang, Optimal Policy for Inventory Management with Periodic and Controlled Resets, arXiv:2209.03571v1, G and the relation below it, p.16

import Mathlib
import Definitions.Def_ResetInventory_ResetModel
import Definitions.Def_ResetInventory_expectedNext

namespace ResetInventory

/-- The function `G(z, t) = c z + H(z, t) + γ E(J((z − w)⁺, t + 1))` of Lee, Mintz, Aswani, Shen,
Yang, arXiv:2209.03571v1, p.16, with the next-period cost-to-go `J(·, t + 1)` passed as `V`.

**Formalization Note** `V` plays `J(·, t + 1)`; the expectation is `expectedNext mdl.f V z`. With
it, the no-reset minimum of (22) equals `min_{z ∈ [x, c_max]} G(z, t) + K·1_{ℝ*₊}(z − x) − c x`
(p.16). -/
noncomputable def costG (mdl : ResetModel) (V : ℝ → ℝ) (t : ℕ) (z : ℝ) : ℝ :=
  mdl.c * z + mdl.H z t + mdl.γ * expectedNext mdl.f V z

end ResetInventory


