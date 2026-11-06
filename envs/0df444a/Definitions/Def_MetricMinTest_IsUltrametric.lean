-- Prove2me | Definitions.Def_MetricMinTest_IsUltrametric
-- name    : MetricMinTest_IsUltrametric
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:52.549383+00:00
-- url     : https://prove2.me/theorems/2f77a2ea-c17f-4252-bf02-71da4a743a53
-- title:
--   Ultrametric
-- statement:
--   A pseudometric $d$ is an **ultrametric** if distinct points are at positive distance and the strong triangle inequality holds:
--   $$d(i,l)\le\max\{d(i,j),\,d(j,l)\}\qquad\text{for all } i,j,l.$$
--   The hierarchical metrics of the paper, in particular the critical metric $d_m$ of Theorem A, are ultrametrics.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Theorem A, p.2; §4.1, p.8

import Mathlib
import Definitions.Def_MetricMinTest_IsPseudometric

namespace MetricMinTest

/-- **Ultrametric.** Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027
submission (manuscript sha256 dcece193…ad32bb), Theorem A p.2 and §4.1 p.8: a metric (distinct
points at positive distance) satisfying the strong triangle inequality
`d(i, l) ≤ max {d(i, j), d(j, l)}`. -/
def IsUltrametric {ι : Type} (d : ι → ι → ℝ) : Prop :=
  IsPseudometric d ∧ (∀ i j, d i j = 0 → i = j) ∧ (∀ i j l, d i l ≤ max (d i j) (d j l))

end MetricMinTest


