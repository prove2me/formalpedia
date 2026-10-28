-- Prove2me | Definitions.Def_D1Bound5_FinitePIntegralRows_Definitions
-- name    : D1Bound5_FinitePIntegralRows_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:06:06.915789+00:00
-- url     : https://prove2.me/theorems/7b38a9c5-46a8-43f2-983a-c27e515b15b2
-- title:
--   Finite PIntegral Rows
-- statement:
--   Definitions for finite pintegral rows in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `finitePLeadingFactor`, `finitePLinearFactor`, `finitePRowForm`.
-- source:
--   D1Bound5/FinitePIntegralRows.lean, lines 10-11, SHA-256 f4ae4543e8d296d5524652a8ec1de382e8c69fd4002555ade9ad3f247eeee37c; D1Bound5/FinitePIntegralRows.lean, lines 13-13, SHA-256 f4ae4543e8d296d5524652a8ec1de382e8c69fd4002555ade9ad3f247eeee37c; D1Bound5/FinitePIntegralRows.lean, lines 126-128, SHA-256 f4ae4543e8d296d5524652a8ec1de382e8c69fd4002555ade9ad3f247eeee37c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FinitePMatrix_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5

def finitePLeadingFactor {R : Type*} [CommRing R] (a b s : R) : R :=
  3*s^2-(a+b)*s-a*b

def finitePLinearFactor {R : Type*} [CommRing R] (a b s : R) : R := 2*s-a-b













def finitePRowForm {R : Type*} [CommRing R]
    (a b s c z rA rB rS : R) (i : Fin 4) : R :=
  (finitePDividedMatrix a b s c).mulVec ![z,rA,rB,rS] i





end D1Bound5
end


