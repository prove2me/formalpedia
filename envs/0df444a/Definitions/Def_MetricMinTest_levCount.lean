-- Prove2me | Definitions.Def_MetricMinTest_levCount
-- name    : MetricMinTest_levCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:59.844388+00:00
-- url     : https://prove2.me/theorems/8666890f-8d59-4376-9b5c-a6cf7fe4ed7a
-- title:
--   Number of points $v_t$ at level $t$
-- statement:
--   From a fixed center of $\{0,\dots,b-1\}^m$, the number of points at level $t$ is $v_0=1$ and $v_t=b^t-b^{t-1}$ for $1\le t\le m$.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), §4.1, p.8

import Mathlib

namespace MetricMinTest

/-- **Number of points at level `t`**, `v₀ = 1`, `v_t = b^t − b^{t−1}`. Chen–Fang,
*Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256
dcece193…ad32bb), §4.1, p.8. -/
noncomputable def levCount (b t : ℕ) : ℝ :=
  if t = 0 then 1 else (b : ℝ) ^ t - (b : ℝ) ^ (t - 1)

end MetricMinTest


