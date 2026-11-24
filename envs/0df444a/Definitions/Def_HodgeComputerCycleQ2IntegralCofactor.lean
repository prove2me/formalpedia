-- Prove2me | Definitions.Def_HodgeComputerCycleQ2IntegralCofactor
-- name    : HodgeComputerCycleQ2IntegralCofactor
-- status  : Definition
-- author  : @pageman
-- created : 2026-11-23T22:51:35.605012+00:00
-- url     : https://prove2.me/theorems/81ad2538-fdeb-4d51-a113-279aaa8c7090
-- title:
--   Integral cofactor of the cycle-q2 source
-- statement:
--   Let $F$ be the cyclic sextic and set $B = A/2$. The factored source is $M \cdot L$ with
--
--   $$M = X_0 X_1^2 X_2^3 Y_0^2 Y_1^2 Y_2, \qquad L = \tfrac12 X_2^3 Y_0 Y_2 - 9 X_0^5.$$
--
--   The identity $\tfrac12 \cdot (-18) = -9$ rewrites $L$ as $\tfrac12 I$, where the cofactor
--
--   $$I = X_2^3 Y_0 Y_2 - 18 X_0^5$$
--
--   has integer coefficients. `integralSource` is $\tfrac12 M I$. `integralResidue(S, W)` is the normal-chart residue of $(F, B, S, W)$ with the undifferentiated source factor replaced by $\tfrac12 M I$.
-- source:
--   Child data for HodgeComputer.CycleQ2.normalChart_factored_source_witness, https://prove2.me/theorems/b05510bf-69e8-48d8-865e-765723de92d3.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2FactoredSource

set_option autoImplicit false
noncomputable section
open HodgeComputer HodgeComputer.CycleQ2 MvPolynomial

/-- Integer cofactor $X_2^3 Y_0 Y_2 - 18 X_0^5$. -/
def HodgeComputer.CycleQ2.integralCofactor : AmbientPoly 5 :=
  X 2 ^ 3 * X 3 * X 5 + C (-18 : ℂ) * X 0 ^ 5

/-- `factoredSource` with the factor $\tfrac12$ pulled out of the cofactor. -/
def HodgeComputer.CycleQ2.integralSource : AmbientPoly 5 :=
  C (2⁻¹ : ℂ) * sourceMonomial * integralCofactor

/-- Residue with the source factor replaced by `integralSource`. -/
def HodgeComputer.CycleQ2.integralResidue (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) :
    AmbientPoly n :=
  let S5 : AmbientPoly 5 := S
  let W5 : Fin 5 → AmbientPoly 5 := fun j => W j
  let src : AmbientPoly 5 := integralSource
  S5 ^ 2 * src +
    (NormalChart.residue (F : AmbientPoly 5) chartPole S5 W5 -
      S5 ^ 2 *
        (NormalChart.normal (F : AmbientPoly 5) * pderiv (0 : Fin 6) chartPole -
          chartPole * pderiv (0 : Fin 6) (NormalChart.normal (F : AmbientPoly 5))))


