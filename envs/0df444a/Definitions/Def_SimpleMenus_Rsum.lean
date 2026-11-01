-- Prove2me | Definitions.Def_SimpleMenus_Rsum
-- name    : SimpleMenus_Rsum
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:35:58.908557+00:00
-- url     : https://prove2.me/theorems/107bfc45-8ba6-4fa7-86ee-0f6e1654efad
-- title:
--   Right-hand side $\sum_{l\in S_j}v_lx_l$ of (4)
-- statement:
--   With $S_j=\{l\in\{1,\dots,n\}: v_l<u_j\}$, the right-hand side of the constraints of (4) is
--
--   $$\sum_{l\in S_j}v_l\,x_l ,$$
--
--   the expected payment of a valuation just below $u_j$.
--
--   **Formalization Note** The inequality $v_l<u_j$ is strict, as printed.
-- source:
--   Wang, The Power of Simple Menus in Robust Selling Mechanisms, arXiv:2310.17392v3, p.11

import Mathlib

namespace SimpleMenus

/-- The right-hand side `Σ_{l ∈ S_j} v_l x_l` of (4), with `S_j = {l | v_l < u_j}`
(Wang, *The Power of Simple Menus in Robust Selling Mechanisms*, arXiv:2310.17392v3, p.11).

Formalization Note: the inequality `v_l < u_j` is strict, as printed (the payment just below
`u_j`). -/
noncomputable def Rsum {n M : ℕ} (v x : Fin n → ℝ) (g : Fin M → ℝ) (j : Fin M) : ℝ :=
  ∑ l, if v l < g j then v l * x l else 0

end SimpleMenus


