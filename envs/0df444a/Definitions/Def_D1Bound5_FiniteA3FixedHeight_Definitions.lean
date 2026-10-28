-- Prove2me | Definitions.Def_D1Bound5_FiniteA3FixedHeight_Definitions
-- name    : D1Bound5_FiniteA3FixedHeight_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:57:06.723317+00:00
-- url     : https://prove2.me/theorems/ff89971c-d837-4148-9917-aee031460400
-- title:
--   Finite A3Fixed Height
-- statement:
--   An exact evaluated-coefficient certificate for A3. Coefficients already include the integer row divisor g; no additional normalization is implicit. The named objects in this bundle include `FiniteA3FixedBound`, `instDecidableFiniteA3FixedBound`.
-- source:
--   D1Bound5/FiniteA3FixedHeight.lean, lines 10-20, SHA-256 2c386b422387df417999a9a829ef11df8e191f7ec898a7c827693af20e95d723; D1Bound5/FiniteA3FixedHeight.lean, lines 22-26, SHA-256 2c386b422387df417999a9a829ef11df8e191f7ec898a7c827693af20e95d723. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Tactic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FiniteA3Coefficients_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt

/-- An exact evaluated-coefficient certificate for A3. Coefficients already
include the integer row divisor g; no additional normalization is implicit. -/
def FiniteA3FixedBound {tau nu : ℤ} (a b : QuadInt tau nu) (M : ℚ)
    (w : Fin 3 → Fin 2 → Fin 4 → ℚ) : Prop :=
  (∀ i j ell, 0 ≤ w i j ell) ∧
  (∀ i j ell,
    ((finiteA3RootCoeff a b i j ell).norm : ℚ) ≤
      if b.norm ≤ 25 then
        (w i j ell)^2*(b.norm : ℚ)^6*1000^(6-2*(ell : ℕ))
      else (w i j ell)^2*(b.norm : ℚ)^(9-(ell : ℕ))*200^(6-2*(ell : ℕ))) ∧
  (∀ i, (101/100 : ℚ)*(∑ j, ∑ ell, w i j ell) < M)

instance {tau nu : ℤ} (a b : QuadInt tau nu) (M : ℚ)
    (w : Fin 3 → Fin 2 → Fin 4 → ℚ) :
    Decidable (FiniteA3FixedBound a b M w) := by
  unfold FiniteA3FixedBound
  infer_instance











end D1Bound5
end


