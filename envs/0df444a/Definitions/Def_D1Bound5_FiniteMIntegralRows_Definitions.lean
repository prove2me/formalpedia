-- Prove2me | Definitions.Def_D1Bound5_FiniteMIntegralRows_Definitions
-- name    : D1Bound5_FiniteMIntegralRows_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:14:48.292306+00:00
-- url     : https://prove2.me/theorems/d8da458a-28f0-4729-b55d-4b62fcf4f931
-- title:
--   Finite MIntegral Rows
-- statement:
--   Definitions for finite mintegral rows in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `finiteMRowForm`.
-- source:
--   D1Bound5/FiniteMIntegralRows.lean, lines 9-11, SHA-256 6a41917e374548988e846d67ca045f1fa413585ce5c57ae666d21b73fb0a0713. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteMMatrix_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5

def finiteMRowForm {R : Type*} [CommRing R]
    (a b s c z rA rB rS : R) (i : Fin 4) : R :=
  (finiteMDividedMatrix a b s c).mulVec ![z,rA,rB,rS] i







end D1Bound5
end


