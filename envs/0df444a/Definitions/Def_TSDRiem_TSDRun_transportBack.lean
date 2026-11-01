-- Prove2me | Definitions.Def_TSDRiem_TSDRun_transportBack
-- name    : TSDRiem_TSDRun_transportBack
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:27:10.468371+00:00
-- url     : https://prove2.me/theorems/97c3edea-93bb-4e03-924d-46e6b225cea6
-- title:
--   Transport $\Gamma^{y^{t,0}}_{y^{t,k-1}}$ back to the start of the inner loop
-- statement:
--   For a run of Algorithm 1, outer iteration $t$ and inner step $k\in[m]$, the **transport back** is the linear isometry
--
--   $$
--   \Gamma^{y^{t,0}}_{y^{t,k-1}} : T_{y^{t,k-1}}M\to T_{y^{t,0}}M
--   $$
--
--   along the geodesic $s\mapsto\operatorname{Exp}_{y^{t,k-1}}(s\,w_{t,k})$ determined by the run's connecting vector $w_{t,k}$. Its inverse is $\Gamma^{y^{t,k-1}}_{y^{t,0}}$, as on p.5.
--
--   It moves the projection $P^{y^{t,k-1}}_k$, which acts on the tangent space where step $k$ starts, to the common tangent space $T_{y^{t,0}}M$ where the gap ensuring condition is checked.
--
--   **Formalization Note** Lean's `k : Fin m` is the paper's step $k+1$.
-- source:
--   Gutman & Ho-Nguyen, Coordinate Descent Without Coordinates, arXiv:1912.10627v3, definition of $P_{t,k}$, p.6; notation $\Gamma^y_x$, p.5

import Mathlib
import Definitions.Def_TSDRiem_RiemSetting
import Definitions.Def_TSDRiem_TSDRun

namespace TSDRiem

/-- The transport `Γ^{y^{t,0}}_{y^{t,k−1}} : T_{y^{t,k−1}}M → T_{y^{t,0}}M` back to the start of
the inner loop, along the geodesic fixed by the run's connecting vector `w t k`.

Gutman & Ho-Nguyen, Coordinate Descent Without Coordinates, arXiv:1912.10627v3, definition of
`P_{t,k}`, p.6; notation `Γ^y_x`, p.5.

Formalization Note: Lean's `k : Fin m` is the paper's `k + 1` (see `TSDRun`). Its inverse
`.symm` is the paper's `Γ^{y^{t,k−1}}_{y^{t,0}} = (Γ^{y^{t,0}}_{y^{t,k−1}})⁻¹` (p.5). -/
def TSDRun.transportBack {M : Type*} [MetricSpace M] {T : M → Type*}
    [∀ x, NormedAddCommGroup (T x)] [∀ x, InnerProductSpace ℝ (T x)]
    [∀ x, FiniteDimensional ℝ (T x)] {S : RiemSetting M T} {grad : (x : M) → T x} {m : ℕ}
    (R : TSDRun S grad m) (t : ℕ) (k : Fin m) :
    T (R.y t k.castSucc) ≃ₗᵢ[ℝ] T (R.y t 0) :=
  S.transport _ _ (R.w t k) (R.w_spec t k)

end TSDRiem


