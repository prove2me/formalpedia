-- Prove2me | Definitions.Def_BinaryQueryLB_rrad
-- name    : BinaryQueryLB_rrad
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:45:21.153916+00:00
-- url     : https://prove2.me/theorems/8a33549d-8941-4c65-9a06-b37240f776f5
-- title:
--   The radial part $r_{\mathrm{rad}}$
-- statement:
--   For $q\in\mathbb R^{2m}$,
--   $$
--   r_{\mathrm{rad}}(q)=\begin{cases} b\,q/\|q\|_2, & \|q\|_2>1,\\ 0, & \|q\|_2\le1.\end{cases}
--   $$
--   It is the gradient of the radial term $b(\|q\|_2-1)_+$ outside the unit ball and $0$ on it.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), §2.3, p.12

import Mathlib
import Definitions.Def_BinaryQueryLB_bConst
import Definitions.Def_BinaryQueryLB_PtSpace

namespace BinaryQueryLB

/-- **The radial part `r_rad`.** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), §2.3, p.12: "The radial part is `r_rad(q) = b q/∥q∥₂` if
`∥q∥₂ > 1` and `r_rad(q) = 0` if `∥q∥₂ ≤ 1`." -/
noncomputable def rrad {m : ℕ} (q : PtSpace m) : PtSpace m :=
  if 1 < ‖q‖ then (bConst m / ‖q‖) • q else 0

end BinaryQueryLB


