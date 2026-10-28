-- Prove2me | Definitions.Def_D1Bound5_FiniteQRowBound_Definitions
-- name    : D1Bound5_FiniteQRowBound_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:26:57.755642+00:00
-- url     : https://prove2.me/theorems/bc0ca3f4-1126-4293-9d58-41fd21df42b3
-- title:
--   Finite QRow Bound
-- statement:
--   Definitions for finite qrow bound in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `finiteQAnchors`, `finiteQRowResidual`.
-- source:
--   D1Bound5/FiniteQRowBound.lean, lines 8-8, SHA-256 791fbd5ab0485888fc2207407e4522dac5c3ad388f70c392e5ef0228d0e3578f; D1Bound5/FiniteQRowBound.lean, lines 10-13, SHA-256 791fbd5ab0485888fc2207407e4522dac5c3ad388f70c392e5ef0228d0e3578f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteQMatrix_Definitions

section
namespace D1Bound5

def finiteQAnchors {R : Type*} (a b s t : R) : Fin 4 → R := ![a,b,s,t]

noncomputable def finiteQRowResidual (a b s t c : ℂ) (i : Fin 5) : ℂ :=
  finiteQDividedMatrix a b s t c i 0 +
    ∑ j : Fin 4, finiteQAnchors a b s t j * finiteQDividedMatrix a b s t c i j.succ *
      ((1+1/(finiteQAnchors a b s t j*c))^(1/2 : ℂ))







end D1Bound5
end


