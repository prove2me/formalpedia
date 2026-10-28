-- Prove2me | Definitions.Def_D1Bound5_FiniteA4FixedHeight_Definitions
-- name    : D1Bound5_FiniteA4FixedHeight_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:51:04.374405+00:00
-- url     : https://prove2.me/theorems/2fb9f47d-30b3-4c65-a267-8cbcf513db59
-- title:
--   Finite A4Fixed Height
-- statement:
--   An exact evaluated-coefficient certificate for A4. Coefficients already include the integer row divisor g; no additional normalization is implicit. The named objects in this bundle include `FiniteA4FixedBound`, `instDecidableFiniteA4FixedBound`.
-- source:
--   D1Bound5/FiniteA4FixedHeight.lean, lines 10-20, SHA-256 9da23d107d5468a905083d70a610cff62cd23f973ea59fa3341b16e9257eb2fb; D1Bound5/FiniteA4FixedHeight.lean, lines 22-26, SHA-256 9da23d107d5468a905083d70a610cff62cd23f973ea59fa3341b16e9257eb2fb. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FiniteA4Coefficients_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt

/-- An exact evaluated-coefficient certificate for A4. Coefficients already
include the integer row divisor g; no additional normalization is implicit. -/
def FiniteA4FixedBound {tau nu : ℤ} (a b : QuadInt tau nu) (M : ℚ)
    (w : Fin 3 → Fin 2 → Fin 5 → ℚ) : Prop :=
  (∀ i j ell, 0 ≤ w i j ell) ∧
  (∀ i j ell,
    ((finiteA4RootCoeff a b i j ell).norm : ℚ) ≤
      if b.norm ≤ 25 then
        (w i j ell)^2*(b.norm : ℚ)^9*1000^(8-2*(ell : ℕ))
      else (w i j ell)^2*(b.norm : ℚ)^(13-(ell : ℕ))*200^(8-2*(ell : ℕ))) ∧
  (∀ i, (101/100 : ℚ)*(∑ j, ∑ ell, w i j ell) < M)

instance {tau nu : ℤ} (a b : QuadInt tau nu) (M : ℚ)
    (w : Fin 3 → Fin 2 → Fin 5 → ℚ) :
    Decidable (FiniteA4FixedBound a b M w) := by
  unfold FiniteA4FixedBound
  infer_instance











end D1Bound5
end


