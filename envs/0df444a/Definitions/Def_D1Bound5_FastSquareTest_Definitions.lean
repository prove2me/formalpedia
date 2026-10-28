-- Prove2me | Definitions.Def_D1Bound5_FastSquareTest_Definitions
-- name    : D1Bound5_FastSquareTest_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T01:26:14.437934+00:00
-- url     : https://prove2.me/theorems/17e2264d-432e-424b-8b06-5741c07ba071
-- title:
--   Fast Square Test
-- statement:
--   Each finite mask records square coordinates modulo k+1. The use of k+1 ensures the residue ring is finite even when the sieve is computed from data. The named objects in this bundle include `coordinateSquareMaskBool`, `CoordinateSquareMaskValid`, `instDecidableCoordinateSquareMaskValid`, `CoordinateSquareSieveValid`, `instDecidableCoordinateSquareSieveValid`, `coordinateSquareSieveBool`, `hasSquareRootFast`.
-- source:
--   D1Bound5/FastSquareTest.lean, lines 7-11, SHA-256 93fb33ff431ce54869bd6adeaf8ad3dbc69d1bda6af9b19b16adf05480dbef74; D1Bound5/FastSquareTest.lean, lines 13-18, SHA-256 93fb33ff431ce54869bd6adeaf8ad3dbc69d1bda6af9b19b16adf05480dbef74; D1Bound5/FastSquareTest.lean, lines 20-23, SHA-256 93fb33ff431ce54869bd6adeaf8ad3dbc69d1bda6af9b19b16adf05480dbef74; D1Bound5/FastSquareTest.lean, lines 37-38, SHA-256 93fb33ff431ce54869bd6adeaf8ad3dbc69d1bda6af9b19b16adf05480dbef74; D1Bound5/FastSquareTest.lean, lines 40-43, SHA-256 93fb33ff431ce54869bd6adeaf8ad3dbc69d1bda6af9b19b16adf05480dbef74; D1Bound5/FastSquareTest.lean, lines 45-47, SHA-256 93fb33ff431ce54869bd6adeaf8ad3dbc69d1bda6af9b19b16adf05480dbef74; D1Bound5/FastSquareTest.lean, lines 58-62, SHA-256 93fb33ff431ce54869bd6adeaf8ad3dbc69d1bda6af9b19b16adf05480dbef74. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions

section
namespace D1Bound5
open QuadInt

/-- Each finite mask records square coordinates modulo k+1. The use of k+1
ensures the residue ring is finite even when the sieve is computed from data. -/
def coordinateSquareMaskBool {tau nu : ℤ} (k mask : ℕ)
    (z : QuadInt tau nu) : Bool :=
  mask.testBit ((z.re : ZMod (k+1)).val*(k+1)+(z.im : ZMod (k+1)).val)

/-- A finite, kernel-checkable completeness assertion for one coordinate mask.
It requires every modular square to be accepted, including the zero square. -/
def CoordinateSquareMaskValid (tau nu : ℤ) (k mask : ℕ) : Prop :=
  ∀ x y : ZMod (k+1),
    mask.testBit ((x*x+(-(nu : ZMod (k+1)))*y*y).val*(k+1)+
      (x*y+y*x+(tau : ZMod (k+1))*y*y).val) = true

instance (tau nu : ℤ) (k mask : ℕ) :
    Decidable (CoordinateSquareMaskValid tau nu k mask) := by
  unfold CoordinateSquareMaskValid
  infer_instance



def CoordinateSquareSieveValid (tau nu : ℤ) (sieve : List (ℕ × ℕ)) : Prop :=
  ∀ item ∈ sieve, CoordinateSquareMaskValid tau nu item.1 item.2

instance (tau nu : ℤ) (sieve : List (ℕ × ℕ)) :
    Decidable (CoordinateSquareSieveValid tau nu sieve) := by
  unfold CoordinateSquareSieveValid
  infer_instance

def coordinateSquareSieveBool {tau nu : ℤ} (sieve : List (ℕ × ℕ))
    (z : QuadInt tau nu) : Bool :=
  sieve.all fun item => coordinateSquareMaskBool item.1 item.2 z



/-- The finite-ring sieve is only a rejection prefilter. Passing is followed
by the full exact root procedure, so no modular pseudoroot is accepted. -/
def hasSquareRootFast {tau nu : ℤ} (sieve : List (ℕ × ℕ))
    (z : QuadInt tau nu) : Bool :=
  coordinateSquareSieveBool sieve z && hasSquareRoot z



end D1Bound5
end


