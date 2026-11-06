-- Prove2me | Definitions.Def_MetricMinTest_kappa
-- name    : MetricMinTest_kappa
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:59.897322+00:00
-- url     : https://prove2.me/theorems/74125c24-c8bd-4e6a-9202-256a4c4873e1
-- title:
--   $\kappa=\sum_t v_t g_t^2$
-- statement:
--   For a gap profile, $\kappa=\sum_{t=0}^m v_tg_t^2$, the common row sum of the information matrix of $d_g$.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), §4.1, p.8

import Mathlib
import Definitions.Def_MetricMinTest_levCount

namespace MetricMinTest

/-- **`κ = ∑_{t=0}^m v_t g_t²`.** Chen–Fang, *Minimum-Mean Testing under Metric Constraints*,
STOC 2027 submission (manuscript sha256 dcece193…ad32bb), §4.1, p.8. -/
noncomputable def kappa (b m : ℕ) (g : ℕ → ℝ) : ℝ :=
  ∑ t ∈ Finset.range (m + 1), levCount b t * g t ^ 2

end MetricMinTest


