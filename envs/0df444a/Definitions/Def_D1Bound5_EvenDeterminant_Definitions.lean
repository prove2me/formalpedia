-- Prove2me | Definitions.Def_D1Bound5_EvenDeterminant_Definitions
-- name    : D1Bound5_EvenDeterminant_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:33:30.628143+00:00
-- url     : https://prove2.me/theorems/e04655d0-799b-48dd-bcf6-f711cdb4b742
-- title:
--   Even Determinant
-- statement:
--   Coefficient reduction modulo two in every integral quadratic model. Its target is a nontrivial rank-two algebra even when it has zero divisors. The named objects in this bundle include `quadraticReductionTwo`.
-- source:
--   D1Bound5/EvenDeterminant.lean, lines 70-78, SHA-256 8be5563bc593805dbec0a0a77973231e6167cbe9b0c64e31ce73f3d46b08cc4c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
open scoped NumberField BigOperators
open Matrix Module

namespace D1Bound5





/-- Coefficient reduction modulo two in every integral quadratic model.
Its target is a nontrivial rank-two algebra even when it has zero divisors. -/
def quadraticReductionTwo (tau nu : ℤ) :
    QuadInt tau nu →+* QuadraticAlgebra (ZMod 2) (-(nu : ZMod 2)) (tau : ZMod 2) where
  toFun z := ⟨(z.re : ZMod 2),(z.im : ZMod 2)⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp [QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]
  map_add' z w := by ext <;> simp
  map_mul' z w := by ext <;> simp





end D1Bound5
end


