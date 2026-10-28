-- Prove2me | Definitions.Def_D1Bound5_FiniteN3FixedHeight_Definitions
-- name    : D1Bound5_FiniteN3FixedHeight_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:50:22.224985+00:00
-- url     : https://prove2.me/theorems/8adbf141-f12f-4bff-b682-25d98edcf4a2
-- title:
--   Finite N3Fixed Height
-- statement:
--   The exact N3 coefficients after division by the integral row factor. The named objects in this bundle include `finiteN3FixedPolynomial`, `FiniteN3FixedBound`, `instDecidableFiniteN3FixedBound`.
-- source:
--   D1Bound5/FiniteN3FixedHeight.lean, lines 10-16, SHA-256 0b044a9920f89d86943094e723cbd783c3c11f89d494288bfcbb6b25925d3410; D1Bound5/FiniteN3FixedHeight.lean, lines 27-37, SHA-256 0b044a9920f89d86943094e723cbd783c3c11f89d494288bfcbb6b25925d3410; D1Bound5/FiniteN3FixedHeight.lean, lines 39-43, SHA-256 0b044a9920f89d86943094e723cbd783c3c11f89d494288bfcbb6b25925d3410. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FiniteHomogeneousTwo_Definitions
import Definitions.Def_D1Bound5_FiniteN3Height_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt

/-- The exact N3 coefficients after division by the integral row factor. -/
def finiteN3FixedPolynomial {R : Type*} [CommRing R] (x y : R)
    (i : Fin 3) (j : Fin 2) : Fin 4 → R :=
  ![finiteHomogeneousTwo 4 (finiteN3Coeff0 i j) x y,
    finiteHomogeneousTwo 5 (finiteN3Coeff1 i j) x y,
    finiteHomogeneousTwo 6 (finiteN3Coeff2 i j) x y,
    finiteHomogeneousTwo 7 (finiteN3Coeff3 i j) x y]




/-- An exact evaluated-coefficient certificate for N3. Coefficients already
include the integer row divisor g; no additional normalization is implicit. -/
def FiniteN3FixedBound {tau nu : ℤ} (a b : QuadInt tau nu) (M : ℚ)
    (w : Fin 3 → Fin 2 → Fin 4 → ℚ) : Prop :=
  (∀ i j ell, 0 ≤ w i j ell) ∧
  (∀ i j ell,
    ((finiteN3FixedPolynomial a b i j ell).norm : ℚ) ≤
      if b.norm ≤ 25 then
        (w i j ell)^2*(b.norm : ℚ)^7*1000^(6-2*(ell : ℕ))
      else (w i j ell)^2*(b.norm : ℚ)^(10-(ell : ℕ))*200^(6-2*(ell : ℕ))) ∧
  (∀ i, (101/100 : ℚ)*(∑ j, ∑ ell, w i j ell) < M)

instance {tau nu : ℤ} (a b : QuadInt tau nu) (M : ℚ)
    (w : Fin 3 → Fin 2 → Fin 4 → ℚ) :
    Decidable (FiniteN3FixedBound a b M w) := by
  unfold FiniteN3FixedBound
  infer_instance











end D1Bound5
end


