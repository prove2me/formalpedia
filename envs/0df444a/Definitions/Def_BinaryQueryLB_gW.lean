-- Prove2me | Definitions.Def_BinaryQueryLB_gW
-- name    : BinaryQueryLB_gW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:47:18.56854+00:00
-- url     : https://prove2.me/theorems/298b966b-69ec-4434-b78b-2555972a3763
-- title:
--   The canonical subgradient $g_W$
-- statement:
--   For $y\in X$ write $\bar y/R=q=(x,z)$. The canonical subgradient is
--   $$
--   g_W(y)=\frac M2\big(v_{i_W(y)}(W)+r_{\mathrm{rad}}(q),\,0\big)\in\mathbb R^d,
--   $$
--   with $d-2m$ coordinates in the zero block. It reports the slope of the active piece with the least index and, outside the unit ball, adds the gradient of the radial term.
--
--   **Formalization Note** If no piece is active (only for $m=0$), the value is $0$.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), §2.3, p.12

import Mathlib
import Definitions.Def_BinaryQueryLB_iW
import Definitions.Def_BinaryQueryLB_rrad
import Definitions.Def_BinaryQueryLB_embedQ
import Definitions.Def_BinaryQueryLB_slope
import Definitions.Def_BinaryQueryLB_ybar

namespace BinaryQueryLB

/-- **The canonical subgradient `g_W`.** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), §2.3, p.12: "For `y ∈ X` write `ȳ/R = q = (x, z)` …
The canonical subgradient is `g_W(y) = (M/2)(v_{i_W(y)}(W) + r_rad(q), 0) ∈ R^d`, with `d − 2m`
coordinates in the zero block."

**Formalization Note.** `q = R⁻¹ • ybar d y`, the slope is `slope i (W i)`, the zero block is
`embedQ`. When no index is active (only possible for `m = 0`) the value is `0`. -/
noncomputable def gW (d : ℕ) (R M : ℝ) (W : Fin (d / 2) → EuclideanSpace ℝ (Fin (d / 2)))
    (y : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  match iW W (R⁻¹ • ybar d y) with
  | some i => (M / 2) • embedQ d (slope i (W i) + rrad (R⁻¹ • ybar d y))
  | none => 0

end BinaryQueryLB


