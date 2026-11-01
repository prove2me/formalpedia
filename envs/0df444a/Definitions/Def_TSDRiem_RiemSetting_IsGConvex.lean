-- Prove2me | Definitions.Def_TSDRiem_RiemSetting_IsGConvex
-- name    : TSDRiem_RiemSetting_IsGConvex
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:27:06.545868+00:00
-- url     : https://prove2.me/theorems/042edeb1-a4e1-4dbc-9bc6-50b3e0a7fcbe
-- title:
--   Geodesic convexity, condition (3)
-- statement:
--   A function $f:M\to\mathbb R$ with gradient field $\nabla f$ is **geodesically convex** (g-convex) if
--
--   $$
--   f(y)\ge f(x)+\langle\nabla f(x),v\rangle_x
--   \qquad\text{for all } x,y\in M \text{ and } v\in\operatorname{Exp}^{-1}_x(y).
--   $$
--
--   This is the first-order characterization of convexity along minimizing geodesics. It is the extra hypothesis under which Theorem 4.5 gives an $O(1/t)$ rate for the optimality gap.
--
--   **Formalization Note** As in condition (2), the gradient field is data; for the paper's objects it is the Riemannian gradient of $f$.
-- source:
--   Gutman & Ho-Nguyen, Coordinate Descent Without Coordinates, arXiv:1912.10627v3, §2, eq. (3), p.5

import Mathlib
import Definitions.Def_TSDRiem_RiemSetting
import Definitions.Def_TSDRiem_RiemSetting_ExpInv

open scoped RealInnerProductSpace

namespace TSDRiem

/-- Geodesic convexity, condition (3): for all `x, y ∈ M` and `v ∈ Exp⁻¹_x(y)`,
`f(y) ≥ f(x) + ⟨∇f(x), v⟩_x`.

Gutman & Ho-Nguyen, Coordinate Descent Without Coordinates, arXiv:1912.10627v3, §2, eq. (3), p.5.

Formalization Note: `grad` is the gradient field, given as data (for the paper's objects, the
Riemannian gradient of `f`). -/
def RiemSetting.IsGConvex {M : Type*} [MetricSpace M] {T : M → Type*}
    [∀ x, NormedAddCommGroup (T x)] [∀ x, InnerProductSpace ℝ (T x)]
    (S : RiemSetting M T) (f : M → ℝ) (grad : (x : M) → T x) : Prop :=
  ∀ x y : M, ∀ v ∈ S.ExpInv x y, f x + ⟪grad x, v⟫ ≤ f y

end TSDRiem


