-- Prove2me | Definitions.Def_D1Bound5_BennettTwoIntegralMatrix_Definitions
-- name    : D1Bound5_BennettTwoIntegralMatrix_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:59:39.195522+00:00
-- url     : https://prove2.me/theorems/25243f4a-39d8-4519-8713-ff8201ad2ae5
-- title:
--   Bennett Two Integral Matrix
-- statement:
--   The actual integral matrix for two anchors, with the manuscript's exact clearing factor and column divisibilities. The named objects in this bundle include `bennettTwoClearedMatrix`.
-- source:
--   D1Bound5/BennettTwoIntegralMatrix.lean, lines 15-18, SHA-256 136894d1b4f549edd11ad783443c9dfcdff9dc56c2e0bd789e83020f9f2279d2. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions

section
namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]



/-- The actual integral matrix for two anchors, with the manuscript's exact
clearing factor and column divisibilities. -/
noncomputable def bennettTwoClearedMatrix (a b c : F) (k : ℕ) : Matrix (Fin 3) (Fin 3) F :=
  Matrix.of fun i j ↦ bennettTwoClearedEntry a b c k i j



end D1Bound5
end


