-- Prove2me | Definitions.Def_D1Bound5_BennettDeterminantFormula_Definitions
-- name    : D1Bound5_BennettDeterminantFormula_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T00:48:57.067986+00:00
-- url     : https://prove2.me/theorems/25959876-9dc6-4cb3-9630-383ac252a75e
-- title:
--   Bennett Determinant Formula
-- statement:
--   The generalized binomial product in the all-order determinant formula. The named objects in this bundle include `bennettBinomialProduct`, `bennettDirectedProduct`.
-- source:
--   D1Bound5/BennettDeterminantFormula.lean, lines 9-11, SHA-256 f98a83f3277331ffd79b4bad983ece2c8026e08c5e60f13dc8b325624528de0f; D1Bound5/BennettDeterminantFormula.lean, lines 13-16, SHA-256 f98a83f3277331ffd79b4bad983ece2c8026e08c5e60f13dc8b325624528de0f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.Ring

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]

/-- The generalized binomial product in the all-order determinant formula. -/
noncomputable def bennettBinomialProduct (n k : ℕ) (ν : F) : F :=
  ∏ v ∈ Finset.range n, Ring.choose ((k : F) + ν - (v : F) * (k : F)) k

/-- Every ordered pair of distinct nodes contributes its reciprocal difference. -/
noncomputable def bennettDirectedProduct {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → F) (k : ℕ) : F :=
  ∏ i, ∏ j ∈ Finset.univ.erase i, ((a i - a j)⁻¹) ^ k











end D1Bound5
end


