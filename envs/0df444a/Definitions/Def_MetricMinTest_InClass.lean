-- Prove2me | Definitions.Def_MetricMinTest_InClass
-- name    : MetricMinTest_InClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:06:53.953019+00:00
-- url     : https://prove2.me/theorems/632cd8eb-8177-4123-b415-5226a0a7cce8
-- title:
--   The admissible class $\mathcal P_d$
-- statement:
--   An instance $P$ belongs to the class
--   $$\mathcal P_d=\{P : |\mu_i-\mu_j|\le d(i,j)\ \text{for all } i,j\}.$$
--   This is the structural assumption the tester may exploit: nearby indices have nearby means.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), §2, p.6

import Mathlib
import Definitions.Def_MetricMinTest_Instance_mean

namespace MetricMinTest

/-- **The class `P_d`.** Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027
submission (manuscript sha256 dcece193…ad32bb), §2 p.6:
`P_d = {P : |µᵢ − µⱼ| ≤ d(i, j) ∀ i, j}`. -/
def InClass {ι : Type} (d : ι → ι → ℝ) (P : Instance ι) : Prop :=
  ∀ i j, |P.mean i - P.mean j| ≤ d i j

end MetricMinTest


