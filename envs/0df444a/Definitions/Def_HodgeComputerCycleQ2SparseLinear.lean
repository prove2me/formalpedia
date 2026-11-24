-- Prove2me | Definitions.Def_HodgeComputerCycleQ2SparseLinear
-- name    : HodgeComputerCycleQ2SparseLinear
-- status  : Definition
-- author  : @pageman
-- created : 2026-11-23T23:29:40.980523+00:00
-- url     : https://prove2.me/theorems/75949ecb-d008-4121-a64b-1721eadb8d99
-- title:
--   Linear carrier of the sparse normal-chart residue
-- statement:
--   For a denominator $S$ and numerator components $W_j$, write $U$ for the undifferentiated source factor $\partial_0 F\cdot\partial_0 B - B\cdot\partial_0\partial_0 F$ of the normal chart, and write $\Delta$ for the two-monomial source
--
--   $$\Delta = -9 X_0^6 X_1^2 X_2^3 Y_0^2 Y_1^2 Y_2 + \tfrac{1}{2} X_0 X_1^2 X_2^6 Y_0^3 Y_1^2 Y_2^2.$$
--
--   $\mathrm{sparseLinear}(S,W)$ is the normal-chart residue of $(F,B,S,W)$ with the term $S^2 U$ removed. Once $S$ is fixed, this expression is linear in the five components $W_j$.
--
--   The carrier puts that linear term first:
--
--   $$\mathrm{sparseCarrier}(S,W) = \mathrm{sparseLinear}(S,W) + S^2\Delta.$$
--
--   It is the sparse residue with the two summands written in the opposite order.
-- source:
--   Child of HodgeComputer.CycleQ2.normalChart_sparse_source_witness, https://prove2.me/theorems/feca3e76-ea56-4c69-820b-2e7f349acc7c. Instance: hodge-computer/sextics data/cycle-q2/instance.rec at 83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2SparseSource

set_option autoImplicit false
noncomputable section
open HodgeComputer HodgeComputer.CycleQ2 MvPolynomial

/-- The part of `NormalChart.residue` that does not contain the undifferentiated
source factor. For fixed `S` it is linear in the numerator components `W`. -/
def HodgeComputer.CycleQ2.sparseLinear (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) :
    AmbientPoly n :=
  let S5 : AmbientPoly 5 := S
  let W5 : Fin 5 → AmbientPoly 5 := fun j => W j
  NormalChart.residue (F : AmbientPoly 5) chartPole S5 W5 -
    S5 ^ 2 *
      (NormalChart.normal (F : AmbientPoly 5) * pderiv (0 : Fin 6) chartPole -
        chartPole * pderiv (0 : Fin 6) (NormalChart.normal (F : AmbientPoly 5)))

/-- `sparseLinear S W + S^2 * sparseSource`, the sparse residue written so the
linear carrier is the first summand. -/
def HodgeComputer.CycleQ2.sparseCarrier (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) :
    AmbientPoly n :=
  let S5 : AmbientPoly 5 := S
  let lin : AmbientPoly 5 := sparseLinear S W
  let src : AmbientPoly 5 := sparseSource
  lin + S5 ^ 2 * src


