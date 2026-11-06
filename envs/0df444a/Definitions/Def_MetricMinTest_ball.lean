-- Prove2me | Definitions.Def_MetricMinTest_ball
-- name    : MetricMinTest_ball
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:43.477141+00:00
-- url     : https://prove2.me/theorems/7fa50bb2-eac1-445b-8f7e-a5e9c620c603
-- title:
--   Closed ball $B(j,r)$
-- statement:
--   For a center $j$ and a radius $r$, the closed ball is $B(j,r)=\{i : d(i,j)\le r\}$, a finite set of indices. A local certificate at $j$ with threshold $r$ excludes a negative mean throughout $B(j,r)$.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), §1.1, p.1; §2, p.6

import Mathlib

namespace MetricMinTest

/-- **Closed ball** `B(j, r) = {i : d(i, j) ≤ r}`. Chen–Fang, *Minimum-Mean Testing under Metric
Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), §2 p.6. -/
noncomputable def ball {ι : Type} [Fintype ι] (d : ι → ι → ℝ) (j : ι) (r : ℝ) : Finset ι :=
  Finset.univ.filter (fun i => d i j ≤ r)

end MetricMinTest


