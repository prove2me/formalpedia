-- Prove2me | Definitions.Def_D1Bound5_PairNegativeIntegerObstruction_Definitions
-- name    : D1Bound5_PairNegativeIntegerObstruction_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:38:26.936978+00:00
-- url     : https://prove2.me/theorems/693bc012-c911-49ef-a628-9e88563ef5ad
-- title:
--   Pair Negative Integer Obstruction
-- statement:
--   A root-free rejection check for negative rational integers. It accepts an obstruction only for the two supported coordinate traces; other traces return false. No square roots, norms, or auxiliary witnesses are computed. The named objects in this bundle include `pairNegativeIntegerObstructionBool`.
-- source:
--   D1Bound5/PairNegativeIntegerObstruction.lean, lines 42-50, SHA-256 099be79d73801fcfb76bdc30024dc74b43ab6bdb2e935fcd75d8e115af902e02. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5







/-- A root-free rejection check for negative rational integers. It accepts
an obstruction only for the two supported coordinate traces; other traces
return false. No square roots, norms, or auxiliary witnesses are computed. -/
def pairNegativeIntegerObstructionBool {tau nu : ℤ}
    (z : QuadInt tau nu) : Bool :=
  decide (z.im = 0 ∧ z.re < 0) &&
    (if tau = 0 then decide (¬ nu ∣ z.re)
     else if tau = 1 then decide (¬ (4 * nu - 1) ∣ z.re)
     else false)



end D1Bound5
end


