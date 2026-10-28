-- Prove2me | Definitions.Def_D1Bound5_UnequalPoleResidual_Definitions
-- name    : D1Bound5_UnequalPoleResidual_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T01:32:29.765901+00:00
-- url     : https://prove2.me/theorems/17505c4e-3845-4ea6-95d6-384981749982
-- title:
--   Unequal Pole Residual
-- statement:
--   The actual local residue polynomial with arbitrary positive pole multiplicities e_j+1. Each Taylor order must be at most the polynomial degree k; equal multiplicities are not required. The named objects in this bundle include `unequalPolePolynomial`.
-- source:
--   D1Bound5/UnequalPoleResidual.lean, lines 11-16, SHA-256 e46f9575bbcd97addd0307c7ad2e250b7b7f566707b1c1322ce262892ab0777e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettLocalResidues_Definitions
import Definitions.Def_D1Bound5_BennettResiduePolynomials_Definitions

section
open Finset

namespace D1Bound5

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The actual local residue polynomial with arbitrary positive pole
multiplicities e_j+1. Each Taylor order must be at most the polynomial
degree k; equal multiplicities are not required. -/
noncomputable def unequalPolePolynomial {F : Type*} [Field F] [CharZero F]
    (a : I → F) (e : I → ℕ) (k : ℕ) (ν : F) (j : I) : Polynomial F :=
  bennettResidueTaylor k (e j) ν (a j) (bennettLocalReciprocal a e j)











end D1Bound5
end


