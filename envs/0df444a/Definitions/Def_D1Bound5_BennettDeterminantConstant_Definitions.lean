-- Prove2me | Definitions.Def_D1Bound5_BennettDeterminantConstant_Definitions
-- name    : D1Bound5_BennettDeterminantConstant_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T00:40:29.068289+00:00
-- url     : https://prove2.me/theorems/ece80d5e-4c68-4c93-93d9-1ed6c48570eb
-- title:
--   Bennett Determinant Constant
-- statement:
--   The arbitrary-order cleared polynomial matrix used in node removal. The named objects in this bundle include `bennettClearedMatrix`.
-- source:
--   D1Bound5/BennettDeterminantConstant.lean, lines 12-15, SHA-256 267ae930e881e7b102ec7dd3ddb0469bc45ab29e4985e0503efec75e7c50bb50. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
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
import Definitions.Def_D1Bound5_BennettClearedResidues_Definitions

section
open Finset

namespace D1Bound5

variable {F I : Type*} [Field F] [CharZero F]
variable [Fintype I] [DecidableEq I]

/-- The arbitrary-order cleared polynomial matrix used in node removal. -/
noncomputable def bennettClearedMatrix (a : I → F) (k : ℕ) (ν : F) :
    Matrix I I (Polynomial F) :=
  Matrix.of fun i j ↦ bennettClearedResidue Finset.univ a k ν i j









end D1Bound5
end


