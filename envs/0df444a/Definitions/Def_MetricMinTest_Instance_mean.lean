-- Prove2me | Definitions.Def_MetricMinTest_Instance_mean
-- name    : MetricMinTest_Instance_mean
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:47.189618+00:00
-- url     : https://prove2.me/theorems/1621fb68-fe6c-4f49-93f1-916853f40296
-- title:
--   Mean $\mu_i$ of an instance
-- statement:
--   The **mean** at index $i$ is $\mu_i=\mathbb E_{X\sim P_i}X=\int x\,dP_i(x)$. Since $P_i$ is supported in $[-1,1]$, $\mu_i\in[-1,1]$.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), §2, p.6

import Mathlib
import Definitions.Def_MetricMinTest_Instance

namespace MetricMinTest

/-- **Mean** `µᵢ = E_{X∼Pᵢ} X`. Chen–Fang, *Minimum-Mean Testing under Metric Constraints*,
STOC 2027 submission (manuscript sha256 dcece193…ad32bb), §2 p.6. The law is supported in
`[−1, 1]`, so the integral is that of a bounded integrable variable. -/
noncomputable def Instance.mean {ι : Type} (P : Instance ι) (i : ι) : ℝ :=
  ∫ x, x ∂(P.law i)

end MetricMinTest


