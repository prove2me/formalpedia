-- Prove2me | Definitions.Def_D1Bound5_FiniteN2Residual_Definitions
-- name    : D1Bound5_FiniteN2Residual_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:27:50.370363+00:00
-- url     : https://prove2.me/theorems/3000cf08-e288-473c-a300-94861e55aa8f
-- title:
--   Finite N2Residual
-- statement:
--   Definitions for finite n2residual in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `finiteN2Residual`.
-- source:
--   D1Bound5/FiniteN2Residual.lean, lines 8-11, SHA-256 09991a5abb38bf67b662f328fce0c115f0f5cfc405bf2c1077362baa797bfe9c. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteN2Matrix_Definitions

section
namespace D1Bound5

noncomputable def finiteN2Residual (x y c : ℂ) (i : Fin 3) : ℂ :=
  finiteN2Constant x y c i +
    x*finiteN2Left x y c i*(1+1/(x*c))^(1/2 : ℂ) +
    y*finiteN2Right x y c i*(1+1/(y*c))^(1/2 : ℂ)













end D1Bound5
end


