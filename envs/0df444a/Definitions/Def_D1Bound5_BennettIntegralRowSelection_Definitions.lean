-- Prove2me | Definitions.Def_D1Bound5_BennettIntegralRowSelection_Definitions
-- name    : D1Bound5_BennettIntegralRowSelection_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:22:31.1619+00:00
-- url     : https://prove2.me/theorems/fc4ac584-cdb3-4f2e-ade4-cb270af07ba6
-- title:
--   Bennett Integral Row Selection
-- statement:
--   The actual two-anchor integral linear form. The powers in columns one and two allow division by the anchors without leaving their integer ring. The named objects in this bundle include `bennettTwoRowForm`.
-- source:
--   D1Bound5/BennettIntegralRowSelection.lean, lines 10-16, SHA-256 9c3c5f22bb6cb848bdf27168f61bbb1b8947f740ff7556d2698f7ee50542b384. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5

/-- The actual two-anchor integral linear form. The powers in columns one
and two allow division by the anchors without leaving their integer ring. -/
noncomputable def bennettTwoRowForm {F : Type*} [Field F] [CharZero F]
    (a b c z sA sB : F) (k : ℕ) (i : Fin 3) : F :=
  bennettTwoClearedEntry a b c k i 0*z +
    bennettTwoClearedEntry a b c k i 1*(sA/a) +
      bennettTwoClearedEntry a b c k i 2*(sB/b)







end D1Bound5
end


