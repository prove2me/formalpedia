-- Prove2me | Definitions.Def_D1Bound5_BennettTwoResidualRate_Definitions
-- name    : D1Bound5_BennettTwoResidualRate_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:05:58.392208+00:00
-- url     : https://prove2.me/theorems/5297a64b-8ecf-4956-a242-3bc18356f6b6
-- title:
--   Bennett Two Residual Rate
-- statement:
--   Definitions for bennett two residual rate in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `bennettTwoResidualRate`, `bennettTwoResidualGammaBound`.
-- source:
--   D1Bound5/BennettTwoResidualRate.lean, lines 7-8, SHA-256 a959de125fdeac3f4cd04800acc29e3af47d9b0e2de609a39d3e257a4ba1c377; D1Bound5/BennettTwoResidualRate.lean, lines 10-14, SHA-256 a959de125fdeac3f4cd04800acc29e3af47d9b0e2de609a39d3e257a4ba1c377. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
namespace D1Bound5

noncomputable def bennettTwoResidualRate (A B C δ : ℝ) : ℝ :=
  27 * B * (A * C - 1) ^ 2 / (16 * A * δ ^ 2)

noncomputable def bennettTwoResidualGammaBound (A B C δ : ℝ) (k : ℕ) : ℝ :=
  (4 * δ ^ 2 / (A * B * C ^ 2)) ^ k *
    (Real.Gamma ((k : ℝ) + 3 / 2) * Real.Gamma (2 * (k : ℝ) - 1 / 2) /
      (Real.pi * Real.Gamma (3 * (k : ℝ) + 1))) /
        (1 - 1 / (A * C)) ^ (2 * (k : ℝ) - 1 / 2)









end D1Bound5
end


