-- Prove2me | Definitions.Def_HodgeComputerCycleQ2ExplicitSource
-- name    : HodgeComputerCycleQ2ExplicitSource
-- status  : Definition
-- author  : @pageman
-- created : 2026-11-23T21:18:54.013859+00:00
-- url     : https://prove2.me/theorems/66d9d025-07dc-459d-9687-83bd05cfc17b
-- title:
--   Explicit source factor of the cycle-q2 normal chart
-- statement:
--   For the cyclic sextic $F$ and the pole parameter $B = A/2$, write $\Delta_0 = \partial_0 F \cdot \partial_0 B - B \cdot \partial_0\partial_0 F$. Expanding the derivatives produces a polynomial `explicitSource` of two grouped monomials, in the coefficient shape left by the product rule. `chartPole` is $B$ as an element of the ambient polynomial ring in six variables. `explicitResidue(S, W)` is the normal-chart residue of $(F, B, S, W)$ with the undifferentiated source factor replaced by `explicitSource`. The two expressions agree once $\partial_0 F \cdot \partial_0 B - B \cdot \partial_0\partial_0 F =$ `explicitSource`.
-- source:
--   hodge-computer/sextics data/cycle-q2/instance.rec at 83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0; NormalChart.residue source factor

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart

set_option autoImplicit false
noncomputable section
open HodgeComputer HodgeComputer.CycleQ2 MvPolynomial

/-- The two-monomial source factor `∂₀F · ∂₀B − B · ∂₀∂₀F`, written in the
normal form produced by expanding the derivatives. -/
def HodgeComputer.CycleQ2.explicitSource : AmbientPoly 5 :=
  X 0 * X 1 ^ 2 * X 3 ^ 3 * X 4 ^ 2 * C (1 / 2 : ℂ) ^ 2 * X 2 ^ 6 * X 5 ^ 2 * 2 -
    X 0 ^ 6 * X 1 ^ 2 * X 3 ^ 2 * X 4 ^ 2 * C (1 / 2 : ℂ) * X 2 ^ 3 * X 5 * 18

/-- `B = A / 2`, the pole parameter of the chart. -/
def HodgeComputer.CycleQ2.chartPole : AmbientPoly 5 :=
  C (2⁻¹ : ℂ) * (A : AmbientPoly 5)

/-- Residue with the source factor replaced by `explicitSource`. -/
def HodgeComputer.CycleQ2.explicitResidue (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) :
    AmbientPoly n :=
  let S5 : AmbientPoly 5 := S
  let W5 : Fin 5 → AmbientPoly 5 := fun j => W j
  let src : AmbientPoly 5 := explicitSource
  S5 ^ 2 * src +
    (NormalChart.residue (F : AmbientPoly 5) chartPole S5 W5 -
      S5 ^ 2 *
        (NormalChart.normal (F : AmbientPoly 5) * pderiv (0 : Fin 6) chartPole -
          chartPole * pderiv (0 : Fin 6) (NormalChart.normal (F : AmbientPoly 5))))


