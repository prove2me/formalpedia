-- Prove2me | Definitions.Def_TSDRiem_TSDRun_seminormP
-- name    : TSDRiem_TSDRun_seminormP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:29:11.70145+00:00
-- url     : https://prove2.me/theorems/d52376f6-7caf-42e6-9a10-2298bb70acf8
-- title:
--   Seminorm $\|\cdot\|_{y^{t,0},\mathcal P}$
-- statement:
--   For a run of Algorithm 1 and outer iteration $t$, the seminorm on $T_{y^{t,0}}M$ induced by the selected projections is
--
--   $$
--   \|v\|_{y^{t,0},\mathcal P}:=\sqrt{\sum_{k\in[m]}\|P_{t,k}v\|^2_{y^{t,0}}} .
--   $$
--
--   It is a norm exactly when the images of the $P_{t,k}$ span $T_{y^{t,0}}M$. The sufficient decrease template (11) is stated in this seminorm, and Proposition 4.2 compares it with $\|\cdot\|_{y^{t,0}}$.
-- source:
--   Gutman & Ho-Nguyen, Coordinate Descent Without Coordinates, arXiv:1912.10627v3, p.6

import Mathlib
import Definitions.Def_TSDRiem_RiemSetting
import Definitions.Def_TSDRiem_TSDRun
import Definitions.Def_TSDRiem_TSDRun_Ptk

namespace TSDRiem

/-- The seminorm `‖v‖_{y^{t,0},P} := √(Σ_{k∈[m]} ‖P_{t,k} v‖²_{y^{t,0}})` on `T_{y^{t,0}}M`.

Gutman & Ho-Nguyen, Coordinate Descent Without Coordinates, arXiv:1912.10627v3, p.6. -/
noncomputable def TSDRun.seminormP {M : Type*} [MetricSpace M] {T : M → Type*}
    [∀ x, NormedAddCommGroup (T x)] [∀ x, InnerProductSpace ℝ (T x)]
    [∀ x, FiniteDimensional ℝ (T x)] {S : RiemSetting M T} {grad : (x : M) → T x} {m : ℕ}
    (R : TSDRun S grad m) (t : ℕ) (v : T (R.y t 0)) : ℝ :=
  Real.sqrt (∑ k, ‖R.Ptk t k v‖ ^ 2)

end TSDRiem


