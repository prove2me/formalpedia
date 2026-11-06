-- Prove2me | Definitions.Def_MetricMinTest_dm
-- name    : MetricMinTest_dm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:08:32.57487+00:00
-- url     : https://prove2.me/theorems/04d170b8-0209-4ecb-8bf7-8a095c2b03b6
-- title:
--   The critical four-ary hierarchy $d_m$
-- statement:
--   The critical four-ary hierarchy is $d_m=d_{4,1/2,m}$ on $k=4^m$ points, that is,
--   $$d_m(x,y)=\gamma\big(1-2^{-\mathrm{lev}(x,y)}\big).$$
--   It is the metric of Theorem A.
--
--   **Formalization Note** Points are $\mathrm{Fin}\,m\to\mathrm{Fin}\,4$; the margin $\gamma$ is an argument.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), §4.1, p.8

import Mathlib
import Definitions.Def_MetricMinTest_geomMetric

namespace MetricMinTest

/-- **The critical four-ary hierarchy `d_m = d_{4,1/2,m}`.** Chen–Fang, *Minimum-Mean Testing
under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), §4.1, p.8:
"The critical four-ary hierarchy is d_m = d_{4,1/2,m}, that is, d_m(x, y) = γ(1 − 2^{−lev(x,y)})",
on `k = 4^m` points.

**Formalization Note.** Points are `Fin m → Fin 4`; `γ` is an argument. -/
noncomputable def dm (m : ℕ) (γ : ℝ) : (Fin m → Fin 4) → (Fin m → Fin 4) → ℝ :=
  geomMetric 4 m (1 / 2) γ

end MetricMinTest


