-- Prove2me | Definitions.Def_TSDRiem_RiemSetting_ExpInv
-- name    : TSDRiem_RiemSetting_ExpInv
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:26:23.334153+00:00
-- url     : https://prove2.me/theorems/11c1c8fe-d805-474d-bebf-ffcdcf52204b
-- title:
--   Set-valued inverse exponential map $\operatorname{Exp}^{-1}_x(y)$ (§2)
-- statement:
--   In a Riemannian setting, the **inverse exponential map** at $x\in M$ is the set-valued map
--
--   $$
--   \operatorname{Exp}^{-1}_x(y)=\operatorname*{arg\,min}_{v\in T_xM}\big\{\|v\|_x : \operatorname{Exp}_x(v)=y\big\},
--   $$
--
--   the set of tangent vectors of least norm among those whose exponential is $y$.
--
--   Under axioms (A1) and (A2) of the setting this set is nonempty and every $v\in\operatorname{Exp}^{-1}_x(y)$ has $\|v\|_x=d(x,y)$, as stated on p.4. It is the vector along which geodesic convexity (3) is tested.
-- source:
--   Gutman & Ho-Nguyen, Coordinate Descent Without Coordinates, arXiv:1912.10627v3, §2, p.4

import Mathlib
import Definitions.Def_TSDRiem_RiemSetting

namespace TSDRiem

/-- The set-valued inverse exponential map
`Exp⁻¹_x(y) = arg min_{v ∈ T_xM} {‖v‖_x : Exp_x(v) = y}`: the tangent vectors at `x` of least
norm among those whose exponential is `y`.

Gutman & Ho-Nguyen, Coordinate Descent Without Coordinates, arXiv:1912.10627v3, §2, p.4. -/
def RiemSetting.ExpInv {M : Type*} [MetricSpace M] {T : M → Type*}
    [∀ x, NormedAddCommGroup (T x)] [∀ x, InnerProductSpace ℝ (T x)]
    (S : RiemSetting M T) (x y : M) : Set (T x) :=
  {v | S.exp x v = y ∧ ∀ w : T x, S.exp x w = y → ‖v‖ ≤ ‖w‖}

end TSDRiem


