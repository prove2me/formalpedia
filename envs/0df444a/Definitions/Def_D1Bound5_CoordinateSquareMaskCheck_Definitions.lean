-- Prove2me | Definitions.Def_D1Bound5_CoordinateSquareMaskCheck_Definitions
-- name    : D1Bound5_CoordinateSquareMaskCheck_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:38:22.350935+00:00
-- url     : https://prove2.me/theorems/ab6a415a-a842-4276-a742-24c81c601f25
-- title:
--   Coordinate Square Mask Check
-- statement:
--   The same mask obligation as CoordinateSquareMaskValid, evaluated by plain integer arithmetic and two List.range traversals. This avoids constructing a nested finite-universal proof over ZMod for every mask. The named objects in this bundle include `coordinateSquareMaskRowCheck`, `coordinateSquareMaskCheck`.
-- source:
--   D1Bound5/CoordinateSquareMaskCheck.lean, lines 5-13, SHA-256 d2d8bc2ee22d2527d31449ebcfb799b981fd548c07c5db168946e1208c6d24cc; D1Bound5/CoordinateSquareMaskCheck.lean, lines 15-16, SHA-256 d2d8bc2ee22d2527d31449ebcfb799b981fd548c07c5db168946e1208c6d24cc. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith

section
namespace D1Bound5

/-- The same mask obligation as CoordinateSquareMaskValid, evaluated by
plain integer arithmetic and two List.range traversals. This avoids
constructing a nested finite-universal proof over ZMod for every mask. -/
def coordinateSquareMaskRowCheck (tau nu : ℤ) (k mask x : ℕ) : Bool :=
  (List.range (k+1)).all fun y =>
    mask.testBit
      (((((x : ℤ)*(x : ℤ)-nu*(y : ℤ)*(y : ℤ)) % (k+1 : ℕ)).toNat)*(k+1)+
        (((x : ℤ)*(y : ℤ)+(y : ℤ)*(x : ℤ)+tau*(y : ℤ)*(y : ℤ)) %
          (k+1 : ℕ)).toNat)

def coordinateSquareMaskCheck (tau nu : ℤ) (k mask : ℕ) : Bool :=
  (List.range (k+1)).all fun x => coordinateSquareMaskRowCheck tau nu k mask x



end D1Bound5

namespace D1Bound5





end D1Bound5
end


