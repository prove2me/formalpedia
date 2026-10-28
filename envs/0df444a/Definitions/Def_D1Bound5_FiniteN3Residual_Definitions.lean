-- Prove2me | Definitions.Def_D1Bound5_FiniteN3Residual_Definitions
-- name    : D1Bound5_FiniteN3Residual_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:58:57.719254+00:00
-- url     : https://prove2.me/theorems/85fa56bb-b8aa-4944-8f3a-fbb8bb732ccf
-- title:
--   Finite N3Residual
-- statement:
--   Definitions for finite n3residual in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `finiteN3Residual`.
-- source:
--   D1Bound5/FiniteN3Residual.lean, lines 10-12, SHA-256 82019ac56278f79ea4d97140058b44fe0991367550cdc22df680f7f4332187b6. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions
import Definitions.Def_D1Bound5_FiniteN3Matrix_Definitions

section
open Polynomial

namespace D1Bound5

noncomputable def finiteN3Residual (x y c : ℂ) (i : Fin 3) : ℂ :=
  ∑ j, finiteN3Matrix x y c i j *
    (1+bennettTwoNodes x y j*(x*y*c)⁻¹)^(1/2 : ℂ)













end D1Bound5
end


