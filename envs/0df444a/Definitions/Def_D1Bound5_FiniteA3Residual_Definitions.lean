-- Prove2me | Definitions.Def_D1Bound5_FiniteA3Residual_Definitions
-- name    : D1Bound5_FiniteA3Residual_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:58:58.354289+00:00
-- url     : https://prove2.me/theorems/e4b2df6b-8458-41ea-b0ef-6652637be0c1
-- title:
--   Finite A3Residual
-- statement:
--   Definitions for finite a3residual in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `finiteA3Residual`.
-- source:
--   D1Bound5/FiniteA3Residual.lean, lines 7-9, SHA-256 b4baf5e62291c792066116902c9dd97737aa2e60d23b97aa569a4defd42d19d0. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions
import Definitions.Def_D1Bound5_FiniteA3Matrix_Definitions

section
namespace D1Bound5

noncomputable def finiteA3Residual (x y c : ℂ) (i : Fin 3) : ℂ :=
  ∑ j, finiteA3Matrix x y c i j*
    (1+bennettTwoNodes x y j*(x*y*c)⁻¹)^(1/2 : ℂ)













end D1Bound5
end


