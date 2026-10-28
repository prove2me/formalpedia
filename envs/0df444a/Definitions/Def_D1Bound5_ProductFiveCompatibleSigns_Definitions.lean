-- Prove2me | Definitions.Def_D1Bound5_ProductFiveCompatibleSigns_Definitions
-- name    : D1Bound5_ProductFiveCompatibleSigns_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:06:19.217383+00:00
-- url     : https://prove2.me/theorems/3ee84ec7-a497-4e93-a50a-918f19d26016
-- title:
--   Product Five Compatible Signs
-- statement:
--   The fifth-column bound takes priority over the mixed prefix bounds. The named objects in this bundle include `FiveSignedEntryGood`.
-- source:
--   D1Bound5/ProductFiveCompatibleSigns.lean, lines 40-49, SHA-256 7ef326eadce635a2fc8001d19ab9a7846a67febccdcf6d3cfe50963ad72c4cef. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_MixedRootMatrixSigns_Definitions

section
namespace D1Bound5



/-- The fifth-column bound takes priority over the mixed prefix bounds. -/
def FiveSignedEntryGood {R : Type*} [CommRing R]
    (f : R →+* ℂ) (a : Fin 5 → R) (u : Fin 5 → ℂ)
    (i j : Fin 5) (r : R) : Prop :=
  if i = 4 ∨ j = 4 then
    SignedEntryBounds f (a i) (a j) (u i) (u j) r (50/99) (625/264627)
  else if i = 0 ∨ j = 0 then
    SignedEntryBounds f (a i) (a j) (u i) (u j) r (5/9) (25/486)
  else
    SignedEntryBounds f (a i) (a j) (u i) (u j) r (7/13) (1/64)













open scoped NumberField
open Module








end D1Bound5
end


