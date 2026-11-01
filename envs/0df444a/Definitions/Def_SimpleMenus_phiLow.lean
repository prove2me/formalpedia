-- Prove2me | Definitions.Def_SimpleMenus_phiLow
-- name    : SimpleMenus_phiLow
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:36:00.328102+00:00
-- url     : https://prove2.me/theorems/6c2e81e1-a77e-4663-859b-2a48d07e7cbf
-- title:
--   Left limits $\underline\phi_{k,j}$ at the grid points
-- statement:
--   At each grid point the paper uses the left limit
--
--   $$\underline\phi_{k,j}=\lim_{w\to u_j-}\phi_k(w),\qquad k=1,\dots,K,\ j=1,\dots,n+m+1 .$$
--
--   These are the coefficients of Problem (4).
--
--   **Formalization Note** The left limit is Mathlib's `Function.leftLim`. At a grid point $u_j=0$ the left limit would look outside $[0,\bar v]$; the value $\phi_k(0)$ is used there (under the breakpoint assumption $\phi_k$ is right-continuous at $0$, and the constraints so generated are the $w=0$ constraints of (3)).
-- source:
--   Wang, The Power of Simple Menus in Robust Selling Mechanisms, arXiv:2310.17392v3, p.11

import Mathlib

namespace SimpleMenus

/-- The left limits `ϕ̲_{k,j} = lim_{w → u_j−} ϕ_k(w)` at the grid points
(Wang, *The Power of Simple Menus in Robust Selling Mechanisms*, arXiv:2310.17392v3, p.11).

Formalization Note: `Function.leftLim` is Mathlib's left limit. At a grid point `u_j = 0` the left
limit would look outside `[0, v̄]`; there the value `ϕ_k(0)` is used (`ϕ_k` is continuous at `0`
from the right under the breakpoint assumption, and the constraints so generated are the `w = 0`
constraints of (3)). -/
noncomputable def phiLow {K M : ℕ} (phi : Fin K → ℝ → ℝ) (g : Fin M → ℝ) (k : Fin K)
    (j : Fin M) : ℝ :=
  if g j = 0 then phi k 0 else Function.leftLim (phi k) (g j)

end SimpleMenus


