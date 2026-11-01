-- Prove2me | Definitions.Def_TSDRiem_TSDRun_Ptk
-- name    : TSDRiem_TSDRun_Ptk
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:28:20.050978+00:00
-- url     : https://prove2.me/theorems/a957bf45-75af-4c26-a6c5-124fe28ec8d7
-- title:
--   Transported projection $P_{t,k}$
-- statement:
--   For a run of Algorithm 1, outer iteration $t$ and inner step $k\in[m]$, the **transported projection** is the operator on $T_{y^{t,0}}M$
--
--   $$
--   P_{t,k}:=\Gamma^{y^{t,0}}_{y^{t,k-1}}\,P^{y^{t,k-1}}_k\,\Gamma^{y^{t,k-1}}_{y^{t,0}} ,
--   $$
--
--   the projection of step $k$ moved to the start of the inner loop. Because the transports are linear isometries, $P_{t,k}$ is again an orthogonal projection.
--
--   The collection $\{P_{t,k}\}_{k\in[m]}$ is compared with an orthogonal decomposition of $T_{y^{t,0}}M$ in the gap ensuring condition, Assumption 4.2.
--
--   **Formalization Note** Lean's `k : Fin m` is the paper's step $k+1$; $P^{y^{t,k-1}}_k$ is the orthogonal projection onto the run's subspace.
-- source:
--   Gutman & Ho-Nguyen, Coordinate Descent Without Coordinates, arXiv:1912.10627v3, p.6

import Mathlib
import Definitions.Def_TSDRiem_RiemSetting
import Definitions.Def_TSDRiem_TSDRun
import Definitions.Def_TSDRiem_TSDRun_transportBack

namespace TSDRiem

/-- The transported projection
`P_{t,k} := Γ^{y^{t,0}}_{y^{t,k−1}} P^{y^{t,k−1}}_k Γ^{y^{t,k−1}}_{y^{t,0}}`, an operator on
`T_{y^{t,0}}M`.

Gutman & Ho-Nguyen, Coordinate Descent Without Coordinates, arXiv:1912.10627v3, p.6.

Formalization Note: Lean's `k : Fin m` is the paper's `k + 1`. `P^{y^{t,k−1}}_k` is the
orthogonal projection onto the run's subspace `sub t k`, and `Γ^{y^{t,k−1}}_{y^{t,0}}` is the
inverse of `transportBack t k`, so `P_{t,k}` is itself an orthogonal projection. -/
noncomputable def TSDRun.Ptk {M : Type*} [MetricSpace M] {T : M → Type*}
    [∀ x, NormedAddCommGroup (T x)] [∀ x, InnerProductSpace ℝ (T x)]
    [∀ x, FiniteDimensional ℝ (T x)] {S : RiemSetting M T} {grad : (x : M) → T x} {m : ℕ}
    (R : TSDRun S grad m) (t : ℕ) (k : Fin m) :
    T (R.y t 0) →L[ℝ] T (R.y t 0) :=
  ((R.transportBack t k : T (R.y t k.castSucc) →L[ℝ] T (R.y t 0)).comp
    (R.sub t k).starProjection).comp
    ((R.transportBack t k).symm : T (R.y t 0) →L[ℝ] T (R.y t k.castSucc))

end TSDRiem


