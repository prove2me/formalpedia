-- Prove2me | Definitions.Def_HodgeComputerCycleQ2FactoredSource
-- name    : HodgeComputerCycleQ2FactoredSource
-- status  : Definition
-- author  : @pageman
-- created : 2026-11-23T22:43:45.886224+00:00
-- url     : https://prove2.me/theorems/d792750e-663a-4269-80e0-d9469af47da3
-- title:
--   Factored source of the cycle-q2 normal chart
-- statement:
--   Let $F$ be the cyclic sextic and set $B = A/2$. The two-monomial source
--
--   $$\Delta = -9 X_0^6 X_1^2 X_2^3 Y_0^2 Y_1^2 Y_2 + \tfrac12 X_0 X_1^2 X_2^6 Y_0^3 Y_1^2 Y_2^2$$
--
--   factors as $M \cdot L$, where
--
--   $$M = X_0 X_1^2 X_2^3 Y_0^2 Y_1^2 Y_2, \qquad L = \tfrac12 X_2^3 Y_0 Y_2 - 9 X_0^5.$$
--
--   `factoredSource` is this product. `factoredResidue(S, W)` is the normal-chart residue of $(F, B, S, W)$ with the undifferentiated source factor replaced by $M \cdot L$.
-- source:
--   Alternative reduction of HodgeComputer.CycleQ2.normalChart_explicit_source_witness. Instance: hodge-computer/sextics data/cycle-q2/instance.rec at 83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2ExplicitSource

set_option autoImplicit false
noncomputable section
open HodgeComputer HodgeComputer.CycleQ2 MvPolynomial

/-- Common monomial factor of the two-term source. -/
def HodgeComputer.CycleQ2.sourceMonomial : AmbientPoly 5 :=
  X 0 * X 1 ^ 2 * X 2 ^ 3 * X 3 ^ 2 * X 4 ^ 2 * X 5

/-- Cofactor $\tfrac12 X_2^3 Y_0 Y_2 - 9 X_0^5$. -/
def HodgeComputer.CycleQ2.sourceCofactor : AmbientPoly 5 :=
  C (2⁻¹ : ℂ) * X 2 ^ 3 * X 3 * X 5 + C (-9 : ℂ) * X 0 ^ 5

/-- `sourceMonomial * sourceCofactor`. -/
def HodgeComputer.CycleQ2.factoredSource : AmbientPoly 5 :=
  sourceMonomial * sourceCofactor

/-- Residue with the source factor replaced by `factoredSource`. -/
def HodgeComputer.CycleQ2.factoredResidue (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) :
    AmbientPoly n :=
  let S5 : AmbientPoly 5 := S
  let W5 : Fin 5 → AmbientPoly 5 := fun j => W j
  let src : AmbientPoly 5 := factoredSource
  S5 ^ 2 * src +
    (NormalChart.residue (F : AmbientPoly 5) chartPole S5 W5 -
      S5 ^ 2 *
        (NormalChart.normal (F : AmbientPoly 5) * pderiv (0 : Fin 6) chartPole -
          chartPole * pderiv (0 : Fin 6) (NormalChart.normal (F : AmbientPoly 5))))


