-- Prove2me | Definitions.Def_D1Bound5_OrdinaryClosedIntervals_Definitions
-- name    : D1Bound5_OrdinaryClosedIntervals_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:28:57.332463+00:00
-- url     : https://prove2.me/theorems/b12a928a-6c96-44bc-8227-940a107d0497
-- title:
--   Ordinary Closed Intervals
-- statement:
--   Definitions for ordinary closed intervals in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `ordinaryWindowLower`, `ordinaryWindowUpper`.
-- source:
--   D1Bound5/OrdinaryClosedIntervals.lean, lines 11-12, SHA-256 2a5f04eb6285acfb92a512be32794797bc3bc72ea1071063ed81f784bc551a9b; D1Bound5/OrdinaryClosedIntervals.lean, lines 14-15, SHA-256 2a5f04eb6285acfb92a512be32794797bc3bc72ea1071063ed81f784bc551a9b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order

section
open scoped NumberField
open Module

namespace D1Bound5

noncomputable def ordinaryWindowLower (B C : ℝ) (k : ℕ) : ℝ :=
  36*(42*B^3*C)^(2*k)*C/(B^2*(1-1/4000 : ℝ))

noncomputable def ordinaryWindowUpper (A B C : ℝ) (k : ℕ) : ℝ :=
  (2*A*C^2/(5*B))^(2*k)/(C*(1+1/4000 : ℝ))









end D1Bound5
end


