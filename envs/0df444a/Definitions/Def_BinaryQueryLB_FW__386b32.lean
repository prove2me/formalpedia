-- Prove2me | Definitions.Def_BinaryQueryLB_FW__386b32
-- name    : BinaryQueryLB_FW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:47:04.750766+00:00
-- url     : https://prove2.me/theorems/386b3232-34d2-438e-b795-8fb0329cd975
-- title:
--   The hard function $F_W$
-- statement:
--   Let $m=\lfloor d/2\rfloor$. For $W\in\mathcal W$ and $y\in\mathbb R^d$,
--   $$
--   F_W(y)=\frac{MR}{2}\,\Phi_W(\bar y/R).
--   $$
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Definition 2.4, p.12

import Mathlib
import Definitions.Def_BinaryQueryLB_PhiW
import Definitions.Def_BinaryQueryLB_ybar

namespace BinaryQueryLB

/-- **The hard function `F_W` (Definition 2.4).** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Definition 2.4, p.12: "define
`F_W(y) = (MR/2) Φ_W(ȳ/R)`", with `m = ⌊d/2⌋`.

**Formalization Note.** `m = d / 2` (natural-number division, `= ⌊d/2⌋`); `ȳ/R` is `R⁻¹ • ȳ`. -/
noncomputable def FW (d : ℕ) (R M : ℝ) (W : Fin (d / 2) → EuclideanSpace ℝ (Fin (d / 2)))
    (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  M * R / 2 * PhiW W (R⁻¹ • ybar d y)

end BinaryQueryLB


