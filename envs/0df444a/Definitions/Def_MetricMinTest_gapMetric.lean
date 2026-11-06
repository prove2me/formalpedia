-- Prove2me | Definitions.Def_MetricMinTest_gapMetric
-- name    : MetricMinTest_gapMetric
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:06:21.433194+00:00
-- url     : https://prove2.me/theorems/3f22235b-ba9e-4c39-82be-83fae78506d0
-- title:
--   Hierarchical metric $d_g$ of a gap profile
-- statement:
--   For a gap profile $g$ with $g_0=\gamma$, the hierarchical metric on $V=\{0,\dots,b-1\}^m$ (with $k=b^m$ points) is
--   $$d_g(x,y)=\gamma-g_{\mathrm{lev}(x,y)}.$$
--   It is an ultrametric, or a pseudometric if $g_1=\gamma$.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), §4.1, p.8

import Mathlib
import Definitions.Def_MetricMinTest_lev

namespace MetricMinTest

/-- **Hierarchical metric of a gap profile**, `d_g(x, y) = γ − g_{lev(x,y)}`. Chen–Fang,
*Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256
dcece193…ad32bb), §4.1, p.8, on `V = {0, …, b − 1}^m` with `k = b^m` points.

**Formalization Note.** `γ = g 0`. -/
def gapMetric (b m : ℕ) (g : ℕ → ℝ) (x y : Fin m → Fin b) : ℝ :=
  g 0 - g (lev x y)

end MetricMinTest


