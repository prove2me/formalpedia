-- Prove2me | Definitions.Def_D1Bound5_PairLightArithmeticBridge_Definitions
-- name    : D1Bound5_PairLightArithmeticBridge_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:12:08.458+00:00
-- url     : https://prove2.me/theorems/1123e4d9-0a75-442c-bf51-fe674cc03994
-- title:
--   Pair Light Arithmetic Bridge
-- statement:
--   Forget only the quadratic-algebra structure, retaining both coordinates. The named objects in this bundle include `pairLightCoordinates`, `pairLightCachedCoordinates`.
-- source:
--   D1Bound5/PairLightArithmeticBridge.lean, lines 6-8, SHA-256 3dadaaf272e22eafa7a7c7429a48fe42dbe591d0dcb73ce8b0f98f6b348b8e51; D1Bound5/PairLightArithmeticBridge.lean, lines 10-13, SHA-256 3dadaaf272e22eafa7a7c7429a48fe42dbe591d0dcb73ce8b0f98f6b348b8e51. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_PairCachedResidues_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5

/-- Forget only the quadratic-algebra structure, retaining both coordinates. -/
def pairLightCoordinates {tau nu : ℤ} (z : QuadInt tau nu) : PairLightCoordinate :=
  (z.re, z.im)

/-- Retain the exact vertex coordinates and the entire supplied signature. -/
def pairLightCachedCoordinates {tau nu : ℤ} (x : PairResidueVertex tau nu) :
    PairLightCachedVertex :=
  (pairLightCoordinates x.vertex, x.signature)





































end D1Bound5
end


