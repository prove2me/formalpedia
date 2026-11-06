-- Prove2me | Definitions.Def_MetricMinTest_geomProfile
-- name    : MetricMinTest_geomProfile
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:57.162237+00:00
-- url     : https://prove2.me/theorems/0025210a-360b-4658-bf8d-0b1a9b49017f
-- title:
--   Geometric gap profile $g_t=\gamma b^{-\alpha t}$
-- statement:
--   For $\alpha>0$, the geometric gap profile is $g_t=\gamma b^{-\alpha t}$, $t=0,1,\dots$.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), §4.1, p.8

import Mathlib

namespace MetricMinTest

/-- **Geometric gap profile** `g_t = γ b^{−αt}`. Chen–Fang, *Minimum-Mean Testing under Metric
Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), §4.1, p.8 ("For α > 0,
the geometric profile g_t = γ b^{−αt} defines the metric d_{b,α,m}"). Real power `rpow`. -/
noncomputable def geomProfile (b : ℕ) (α γ : ℝ) (t : ℕ) : ℝ :=
  γ * (b : ℝ) ^ (-(α * t))

end MetricMinTest


