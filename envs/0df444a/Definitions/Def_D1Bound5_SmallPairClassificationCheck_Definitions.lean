-- Prove2me | Definitions.Def_D1Bound5_SmallPairClassificationCheck_Definitions
-- name    : D1Bound5_SmallPairClassificationCheck_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:16:14.832403+00:00
-- url     : https://prove2.me/theorems/a52023ad-d4b3-413b-aef1-dfabac2a6826
-- title:
--   Small Pair Classification Check
-- statement:
--   Complete classification checker for nondegenerate compatible small pairs. The named objects in this bundle include `pairCoordinates`, `smallPairClassifiedBool`.
-- source:
--   D1Bound5/SmallPairClassificationCheck.lean, lines 7-8, SHA-256 13b30ee79d1344410e8883c71036e3d9b17e9072cb676e51f16a84aa1a8cfd5a; D1Bound5/SmallPairClassificationCheck.lean, lines 10-19, SHA-256 13b30ee79d1344410e8883c71036e3d9b17e9072cb676e51f16a84aa1a8cfd5a. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions

section
namespace D1Bound5
open QuadInt

def pairCoordinates {tau nu : ℤ} (a b : QuadInt tau nu) : Finset (ℤ × ℤ) :=
  {(a.re,a.im), (b.re,b.im)}

/-- Complete classification checker for nondegenerate compatible small pairs. -/
def smallPairClassifiedBool {tau nu : ℤ} (xs : List (QuadInt tau nu))
    (rows : List (Finset (ℤ × ℤ))) : Bool :=
  xs.all fun a =>
    if decide (a ≠ 0) then
      xs.all fun b =>
        if decide (b ≠ 0 ∧ a ≠ b ∧ a*b+1 ≠ 0) then
          if hasSquareRoot (a*b+1) then decide (pairCoordinates a b ∈ rows) else true
        else true
    else true



end D1Bound5
end


