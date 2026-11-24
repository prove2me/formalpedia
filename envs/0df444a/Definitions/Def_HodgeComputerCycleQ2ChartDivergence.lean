-- Prove2me | Definitions.Def_HodgeComputerCycleQ2ChartDivergence
-- name    : HodgeComputerCycleQ2ChartDivergence
-- status  : Definition
-- author  : @pageman
-- created : 2026-11-23T23:38:06.869938+00:00
-- url     : https://prove2.me/theorems/5204b2c5-4e9d-4d6f-b7e3-b84e91c9c306
-- title:
--   Chart divergence of the sparse normal-chart residue
-- statement:
--   Let $F$ be the cyclic sextic and let $B = A/2$ be the pole of the normal chart. For a denominator $S$ and numerator components $W_0,\ldots,W_4$, the chart divergence is the sum of the five terms linear in those components:
--
--   $$\sum_{j=0}^{4}\Big((\partial_0 F)^2 S\,\partial_{j+1} W_j - (\partial_0 F)\, S\,(\partial_{j+1} F)\,\partial_0 W_j+ \big(\partial_{j+1} F\cdot(S\,\partial_0\partial_0 F + \partial_0 F\,\partial_0 S) - \partial_0 F\cdot(S\,\partial_{j+1}\partial_0 F + \partial_0 F\,\partial_{j+1} S)\big) W_j\Big).$$
--
--   Write $\Delta$ for the two-monomial source. The divergence carrier is that sum plus the quadratic source term,
--
--   $$\mathrm{divergenceCarrier}(S,W) = \mathrm{chartDivergence}(S,W) + S^2\Delta.$$
--
--   The sum is the part of the normal-chart residue that remains after the undifferentiated source factor $S^2(\partial_0 F\cdot\partial_0 B - B\cdot\partial_0\partial_0 F)$ is removed.
-- source:
--   Child of HodgeComputer.CycleQ2.normalChart_sparse_linear_membership, https://prove2.me/theorems/e160c92a-a560-4c02-822f-2583a4b40581. Instance: hodge-computer/sextics data/cycle-q2/instance.rec at 83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2SparseSource

set_option autoImplicit false
noncomputable section
open HodgeComputer HodgeComputer.CycleQ2 HodgeComputer.NormalChart MvPolynomial
open scoped BigOperators

/-- The summand of `NormalChart.residue` that is linear in the numerator `W`. -/
def HodgeComputer.CycleQ2.chartDivergence (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) :
    AmbientPoly n :=
  let S5 : AmbientPoly 5 := S
  let W5 : Fin 5 → AmbientPoly 5 := fun j => W j
  let F5 : AmbientPoly 5 := F
  ∑ j : Fin 5,
    (normal F5 ^ 2 * S5 * pderiv j.succ (W5 j) -
      normal F5 * S5 * pderiv j.succ F5 * pderiv (0 : Fin 6) (W5 j) +
      (pderiv j.succ F5 * (S5 * pderiv (0 : Fin 6) (normal F5) + normal F5 * pderiv (0 : Fin 6) S5) -
        normal F5 * (S5 * pderiv j.succ (normal F5) + normal F5 * pderiv j.succ S5)) * W5 j)

/-- `chartDivergence S W + S^2 * sparseSource`. -/
def HodgeComputer.CycleQ2.divergenceCarrier (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) :
    AmbientPoly n :=
  let S5 : AmbientPoly 5 := S
  let div : AmbientPoly 5 := chartDivergence S W
  let src : AmbientPoly 5 := sparseSource
  div + S5 ^ 2 * src


