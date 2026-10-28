-- Prove2me | Definitions.Def_D1Bound5_FiniteMResidualPoint_Definitions
-- name    : D1Bound5_FiniteMResidualPoint_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:26:26.7258+00:00
-- url     : https://prove2.me/theorems/a2ce3f3e-c7a7-4b29-a6a6-6f01e3f76af2
-- title:
--   Finite MResidual Point
-- statement:
--   Definitions for finite mresidual point in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `finiteMResidual`.
-- source:
--   D1Bound5/FiniteMResidualPoint.lean, lines 9-11, SHA-256 f7bb209498622e9e35161ef7d6d2d014918b6ada1ab43bba06f6efcfedaca12e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
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
import Definitions.Def_D1Bound5_FiniteMBennettIdentity_Definitions
import Definitions.Def_D1Bound5_FiniteMMatrix_Definitions

section
open Finset Polynomial

namespace D1Bound5

noncomputable def finiteMResidual (a b s c : ℂ) (i : Fin 4) : ℂ :=
  ∑ j, finiteMMatrix a b s c i j *
    (1+finiteMNodes a b s j*(a*b*s*c)⁻¹)^(1/2 : ℂ)









end D1Bound5
end


