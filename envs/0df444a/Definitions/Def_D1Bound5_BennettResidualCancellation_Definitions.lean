-- Prove2me | Definitions.Def_D1Bound5_BennettResidualCancellation_Definitions
-- name    : D1Bound5_BennettResidualCancellation_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T01:28:09.682979+00:00
-- url     : https://prove2.me/theorems/3a6f00f8-bf9e-4e37-b600-cc0edc5ff6aa
-- title:
--   Bennett Residual Cancellation
-- statement:
--   The original arbitrary-order matrix of polynomial residues. The named objects in this bundle include `bennettPolynomialMatrix`.
-- source:
--   D1Bound5/BennettResidualCancellation.lean, lines 145-148, SHA-256 0e8f4d1dac16aef29c7622ad8fa6e48d05646e38a9ebaf133da673991996797d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettResiduePolynomials_Definitions

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]



section Nodes

variable {I : Type*} [Fintype I] [DecidableEq I]







/-- The original arbitrary-order matrix of polynomial residues. -/
noncomputable def bennettPolynomialMatrix (a : I → F) (k : ℕ) (ν : F) :
    Matrix I I (Polynomial F) :=
  Matrix.of fun i j ↦ bennettPolynomialResidue Finset.univ a k ν i j



end Nodes

end D1Bound5
end


