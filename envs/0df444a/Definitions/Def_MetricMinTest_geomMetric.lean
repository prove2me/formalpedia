-- Prove2me | Definitions.Def_MetricMinTest_geomMetric
-- name    : MetricMinTest_geomMetric
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:07:22.001211+00:00
-- url     : https://prove2.me/theorems/785a9cbf-a22b-4cf3-8ad9-74c15603f208
-- title:
--   The metric $d_{b,\alpha,m}$
-- statement:
--   The metric of the geometric profile is
--   $$d_{b,\alpha,m}(x,y)=\gamma\big(1-b^{-\alpha\,\mathrm{lev}(x,y)}\big)$$
--   on $\{0,\dots,b-1\}^m$. The critical exponent is $\alpha=1/2$.
--
--   **Formalization Note** The margin $\gamma$ is an argument.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), §1.2, p.2; §4.1, p.8

import Mathlib
import Definitions.Def_MetricMinTest_gapMetric
import Definitions.Def_MetricMinTest_geomProfile

namespace MetricMinTest

/-- **The metric `d_{b,α,m}`.** Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC
2027 submission (manuscript sha256 dcece193…ad32bb), §4.1 p.8 and §1.2 p.2:
`d_{b,α,m}(x, y) = γ(1 − b^{−α lev(x,y)})`, the metric of the geometric gap profile
`g_t = γ b^{−αt}` on `{0, …, b − 1}^m`.

**Formalization Note.** The margin `γ` is an argument (the metric depends on it). -/
noncomputable def geomMetric (b m : ℕ) (α γ : ℝ) : (Fin m → Fin b) → (Fin m → Fin b) → ℝ :=
  gapMetric b m (geomProfile b α γ)

end MetricMinTest


