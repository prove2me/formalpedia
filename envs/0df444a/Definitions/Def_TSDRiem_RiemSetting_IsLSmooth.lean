-- Prove2me | Definitions.Def_TSDRiem_RiemSetting_IsLSmooth
-- name    : TSDRiem_RiemSetting_IsLSmooth
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:26:21.778906+00:00
-- url     : https://prove2.me/theorems/3af289f4-6a0e-40ea-aca1-6460aa93db6b
-- title:
--   $L_f$-smoothness, condition (2)
-- statement:
--   Let $\nabla f$ be a gradient field, i.e. a choice of vector $\nabla f(x)\in T_xM$ at every point. It is **$L_f$-smooth** if
--
--   $$
--   \|\Gamma^y_x\nabla f(x)-\nabla f(y)\|_y\le L_f\,d(x,y)
--   \qquad\text{for all } x\in M,\ v\in T_xM,\ y=\operatorname{Exp}_x(v),
--   $$
--
--   where $\Gamma^y_x$ is the transport along $t\mapsto\operatorname{Exp}_x(tv)$. This is the Riemannian analogue of a Lipschitz gradient, and it is the standing smoothness assumption of the deterministic analysis in §4.1.
--
--   **Formalization Note** The gradient field is data. For the paper's objects it is the Riemannian gradient of $f$, defined by $\langle\nabla f(x),v\rangle_x=df_x v$.
-- source:
--   Gutman & Ho-Nguyen, Coordinate Descent Without Coordinates, arXiv:1912.10627v3, §2, eq. (2), p.5

import Mathlib
import Definitions.Def_TSDRiem_RiemSetting

namespace TSDRiem

/-- `L_f`-smoothness, condition (2): for all `x ∈ M`, `v ∈ T_xM` and `y = Exp_x(v)`,
`‖Γ^y_x ∇f(x) − ∇f(y)‖_y ≤ L_f d(x, y)`.

Gutman & Ho-Nguyen, Coordinate Descent Without Coordinates, arXiv:1912.10627v3, §2, eq. (2), p.5.

Formalization Note: the gradient `grad : (x : M) → T x` is data (a vector field); for the
paper's objects it is the Riemannian gradient `∇f` of `f`. Quantifying over `y` with a proof of
`exp x v = y` is the same as setting `y = Exp_x(v)`. -/
def RiemSetting.IsLSmooth {M : Type*} [MetricSpace M] {T : M → Type*}
    [∀ x, NormedAddCommGroup (T x)] [∀ x, InnerProductSpace ℝ (T x)]
    (S : RiemSetting M T) (grad : (x : M) → T x) (Lf : ℝ) : Prop :=
  ∀ (x y : M) (v : T x) (h : S.exp x v = y),
    ‖S.transport x y v h (grad x) - grad y‖ ≤ Lf * dist x y

end TSDRiem


