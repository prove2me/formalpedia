-- Prove2me | Definitions.Def_D1Bound5_CoherentRetainedMixedForms_Definitions
-- name    : D1Bound5_CoherentRetainedMixedForms_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:30:38.367043+00:00
-- url     : https://prove2.me/theorems/9049adf9-bdce-4319-979f-358b4a4d27ce
-- title:
--   Coherent Retained Mixed Forms
-- statement:
--   The two exact manuscript interpolation rows. The named objects in this bundle include `CoherentRetainedRow`.
-- source:
--   D1Bound5/CoherentRetainedMixedForms.lean, lines 9-12, SHA-256 eb96a42cf210b66dfcce899bd150fc1582a3f153a19beef7c93531438f527556. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5

/-- The two exact manuscript interpolation rows. -/
def CoherentRetainedRow (H lam U : ℝ) : Prop :=
  (H = 32 ∧ lam = 1/10 ∧ U = 179/10) ∨
    (H = 48 ∧ lam = 19/200 ∧ U = 15)





end D1Bound5
end


