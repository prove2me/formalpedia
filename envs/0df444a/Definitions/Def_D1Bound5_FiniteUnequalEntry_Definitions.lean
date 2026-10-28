-- Prove2me | Definitions.Def_D1Bound5_FiniteUnequalEntry_Definitions
-- name    : D1Bound5_FiniteUnequalEntry_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T01:28:05.953246+00:00
-- url     : https://prove2.me/theorems/e642b23f-1684-4db4-8fb4-2c3b173c5bab
-- title:
--   Finite Unequal Entry
-- statement:
--   The actual cleared residue entry for pole orders (m,k,k), before dividing rows by delta,x,y and the family's common integer g. The named objects in this bundle include `finiteUnequalOrders`, `finiteUnequalClearedEntry`.
-- source:
--   D1Bound5/FiniteUnequalEntry.lean, lines 14-15, SHA-256 4a25eb90becd225388fecc7352da19731da09bdef68e85c87dced6c4c45eeb61; D1Bound5/FiniteUnequalEntry.lean, lines 56-63, SHA-256 4a25eb90becd225388fecc7352da19731da09bdef68e85c87dced6c4c45eeb61. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_BennettClearedResidues_Definitions
import Definitions.Def_D1Bound5_BennettLocalResidues_Definitions
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions

section
open Finset

namespace D1Bound5

def finiteUnequalOrders (k m : ℕ) (i j : Fin 3) : ℕ :=
  ![m,k,k] j + (if i=j then 1 else 0)-1







variable {F : Type*} [Field F] [CharZero F]







/-- The actual cleared residue entry for pole orders (m,k,k), before
dividing rows by delta,x,y and the family's common integer g. -/
noncomputable def finiteUnequalClearedEntry (x y c : F) (k m : ℕ) (i j : Fin 3) : F :=
  (4^k*x^m*y^m*(x-y)^(2*k))*
    (bennettClearedTaylor k (finiteUnequalOrders k m i j) (1/2 : F)
      (bennettTwoNodes x y j)
      (bennettLocalReciprocal (bennettTwoNodes x y) (finiteUnequalOrders k m i) j)).eval
        (x*y*c)







end D1Bound5
end


