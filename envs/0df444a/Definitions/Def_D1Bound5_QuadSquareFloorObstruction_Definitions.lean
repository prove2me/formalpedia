-- Prove2me | Definitions.Def_D1Bound5_QuadSquareFloorObstruction_Definitions
-- name    : D1Bound5_QuadSquareFloorObstruction_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:35:09.53091+00:00
-- url     : https://prove2.me/theorems/23e2857c-bda9-43d4-a6de-61b01cfd4f25
-- title:
--   Quad Square Floor Obstruction
-- statement:
--   Check one natural-number floor witness for a radicand. The branch is determined entirely by the radicand and coordinate ring: nonreal radicands use the norm, positive real ones use the ordinary square gap, and negative real ones use the exact trace-zero or trace-one scale. The named objects in this bundle include `QuadInt.floorObstructionBool`.
-- source:
--   D1Bound5/QuadSquareFloorObstruction.lean, lines 86-101, SHA-256 189bc6919f96623fb014a3f2f03e165069f8dce0da25caec94ef0406cc2c9b3e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5











namespace QuadInt





/-- Check one natural-number floor witness for a radicand. The branch
is determined entirely by the radicand and coordinate ring: nonreal
radicands use the norm, positive real ones use the ordinary square gap,
and negative real ones use the exact trace-zero or trace-one scale. -/
def floorObstructionBool {tau nu : ℤ} (z : QuadInt tau nu) (k : ℕ) : Bool :=
  if z.im = 0 then
    if 0 < z.re then
      decide ((k : ℤ) ^ 2 < z.re ∧ z.re < ((k : ℤ) + 1) ^ 2)
    else if tau = 0 then
      decide (nu * (k : ℤ) ^ 2 < -z.re ∧ -z.re < nu * ((k : ℤ) + 1) ^ 2)
    else if tau = 1 then
      decide ((4 * nu - 1) * (k : ℤ) ^ 2 < -z.re ∧
        -z.re < (4 * nu - 1) * ((k : ℤ) + 1) ^ 2)
    else false
  else
    decide ((k : ℤ) ^ 2 < z.norm ∧ z.norm < ((k : ℤ) + 1) ^ 2)



end QuadInt
end D1Bound5
end


