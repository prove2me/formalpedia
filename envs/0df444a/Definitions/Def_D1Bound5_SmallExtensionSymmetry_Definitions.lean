-- Prove2me | Definitions.Def_D1Bound5_SmallExtensionSymmetry_Definitions
-- name    : D1Bound5_SmallExtensionSymmetry_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:51:05.453554+00:00
-- url     : https://prove2.me/theorems/98915f94-627c-47d6-8bc0-915112d5e052
-- title:
--   Small Extension Symmetry
-- statement:
--   A proper further common extension. Only the final extension is required to be nonzero and outside the anchors; mutation intermediates are not. The named objects in this bundle include `ProperCommonExtension`, `SmallTripleExtensionProperty`, `smallExtensionSymmetry`, `smallCoordinateSet`.
-- source:
--   D1Bound5/SmallExtensionSymmetry.lean, lines 10-14, SHA-256 67e063ccef711bfed6c0611c0e702166cb5f5a03a9533a5385fe57ef43b16f48; D1Bound5/SmallExtensionSymmetry.lean, lines 16-21, SHA-256 67e063ccef711bfed6c0611c0e702166cb5f5a03a9533a5385fe57ef43b16f48; D1Bound5/SmallExtensionSymmetry.lean, lines 61-64, SHA-256 67e063ccef711bfed6c0611c0e702166cb5f5a03a9533a5385fe57ef43b16f48; D1Bound5/SmallExtensionSymmetry.lean, lines 124-126, SHA-256 67e063ccef711bfed6c0611c0e702166cb5f5a03a9533a5385fe57ef43b16f48. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt

/-- A proper further common extension. Only the final extension is required
to be nonzero and outside the anchors; mutation intermediates are not. -/
def ProperCommonExtension {R : Type*} [CommRing R] [DecidableEq R]
    (A : Finset R) (z : R) : Prop :=
  z ≠ 0 ∧ z ∉ A ∧ ∀ a ∈ A, ∃ r : R, r*r = a*z+1

/-- The two facts extracted from the finite radius-10^40 certificates. -/
def SmallTripleExtensionProperty {tau nu : ℤ}
    (A : Finset (QuadInt tau nu)) : Prop :=
  (∀ z, ProperCommonExtension A z → z.norm ≤ 10^80 → z.norm < 85^2) ∧
  (∀ z w, ProperCommonExtension A z → ProperCommonExtension A w →
    z.norm ≤ 10^80 → w.norm ≤ 10^80 → z = w)





/-- Simultaneous sign and coordinate conjugation, encoded independently. -/
def smallExtensionSymmetry {tau nu : ℤ} (sgn conj : Bool)
    (z : QuadInt tau nu) : QuadInt tau nu :=
  if sgn then -(if conj then star z else z) else (if conj then star z else z)











/-- Decode an unordered set of integer coordinate pairs into the ring. -/
def smallCoordinateSet (tau nu : ℤ) (row : Finset (ℤ × ℤ)) :
    Finset (QuadInt tau nu) := row.image (fun p => ⟨p.1, p.2⟩)





end D1Bound5
end


