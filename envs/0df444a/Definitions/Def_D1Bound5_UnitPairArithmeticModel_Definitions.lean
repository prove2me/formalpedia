-- Prove2me | Definitions.Def_D1Bound5_UnitPairArithmeticModel_Definitions
-- name    : D1Bound5_UnitPairArithmeticModel_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:11:37.728097+00:00
-- url     : https://prove2.me/theorems/c0e7653f-a951-4be7-ad92-6b928480717d
-- title:
--   Unit Pair Arithmetic Model
-- statement:
--   One fixed coordinate model carries all the arithmetic needed for the unit-pair reduction. In particular the negative-square parameter is the same parameter as the Pell equations. The named objects in this bundle include `UnitPairArithmeticModel`, `UnitPairArithmeticModel.conjugate`, `UnitPairArithmeticModel.d`, `UnitPairArithmeticModel.w`, `UnitPairArithmeticModel.mapEquiv`, `unitPairTraceZeroModel`, `unitPairTraceOneModel`.
-- source:
--   D1Bound5/UnitPairArithmeticModel.lean, lines 10-24, SHA-256 31a0d8a0d8b8fb8a155f4aa1757650bb63a56b886b27a1d3631ee72dcc025fb7; D1Bound5/UnitPairArithmeticModel.lean, lines 26-48, SHA-256 31a0d8a0d8b8fb8a155f4aa1757650bb63a56b886b27a1d3631ee72dcc025fb7; D1Bound5/UnitPairArithmeticModel.lean, lines 50-68, SHA-256 31a0d8a0d8b8fb8a155f4aa1757650bb63a56b886b27a1d3631ee72dcc025fb7; D1Bound5/UnitPairArithmeticModel.lean, lines 70-89, SHA-256 31a0d8a0d8b8fb8a155f4aa1757650bb63a56b886b27a1d3631ee72dcc025fb7. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FullRingRationalSquares_Definitions
import Definitions.Def_D1Bound5_FullRingUnitPairPell_Definitions
import Definitions.Def_D1Bound5_OneThreeNegative_Definitions
import Definitions.Def_D1Bound5_UnitPairPellBounds_Definitions
import Definitions.Def_D1Bound5_UnitPairPellClassification_Definitions

section
open scoped NumberField QuadraticAlgebra
open Module

namespace D1Bound5

/-- One fixed coordinate model carries all the arithmetic needed for the
unit-pair reduction. In particular the negative-square parameter is the
same parameter as the Pell equations. -/
structure UnitPairArithmeticModel (R : Type*) [CommRing R] where
  d : ℤ
  positive : 0 < d
  squarefree : Squarefree d
  w : R
  square : w * w = -(d : R)
  conjugate : R →+* R
  conjugate_w : conjugate w = -w
  negative_square : ∀ m : ℤ, m ≤ 0 → (∃ r : R, r*r = (m : R)) →
    ∃ y : ℤ, m = -d*y^2
  pell : ∀ z r s : R, z ≠ 0 → r*r = z+1 → s*s = 1-z →
    UnitPairPellDescription d w z

/-- Coordinate transport preserves all square witnesses, and the same
conjugation and field parameter are used for every element. -/
def UnitPairArithmeticModel.mapEquiv {R S : Type*} [CommRing R] [CommRing S]
    (M : UnitPairArithmeticModel R) (e : R ≃+* S) : UnitPairArithmeticModel S where
  d := M.d
  positive := M.positive
  squarefree := M.squarefree
  w := e M.w
  square := by simpa only [map_mul, map_neg, map_intCast] using congrArg e M.square
  conjugate := e.toRingHom.comp (M.conjugate.comp e.symm.toRingHom)
  conjugate_w := by simp [M.conjugate_w]
  negative_square := by
    intro m hm hs
    exact M.negative_square m hm (integer_square_under_ring_equiv e m hs)
  pell := by
    intro z r s hz hr hs
    have h := M.pell (e.symm z) (e.symm r) (e.symm s)
      (by simpa using hz)
      (by simpa only [map_mul, map_add, map_one] using congrArg e.symm hr)
      (by simpa only [map_mul, map_sub, map_one] using congrArg e.symm hs)
    have hmapped : UnitPairPellDescription M.d (e M.w) (e (e.symm z)) :=
      UnitPairPellDescription.map e.toRingHom M.d M.w (e.symm z) h
    simpa only [RingEquiv.apply_symm_apply] using hmapped

 def unitPairTraceZeroModel (d : ℤ) (hd : 0 < d) (hsq : Squarefree d) :
    UnitPairArithmeticModel (QuadInt 0 d) where
  d := d
  positive := hd
  squarefree := hsq
  w := QuadraticAlgebra.omega
  square := by ext <;> simp [QuadraticAlgebra.omega]
  conjugate := starRingEnd (QuadInt 0 d)
  conjugate_w := by ext <;> simp [starRingEnd_apply, QuadraticAlgebra.omega]
  negative_square := fun _ hm hs => nonpositive_integer_square_trace_zero hm hs
  pell := by
    intro z r s hz hr hs
    rcases QuadInt.unit_pair_integer_basis_pell hd z r s hz hr hs with h | h
    · exact Or.inl h
    · right
      obtain ⟨u,v,hv,hPell,hz⟩ := h
      refine ⟨u,v,hv,hPell,?_⟩
      rw [hz]
      ext <;> simp [QuadraticAlgebra.omega]

 def unitPairTraceOneModel (nu : ℤ)
    (hd : 0 < QuadInt.discriminant 1 nu) (hsq : Squarefree (4*nu-1)) :
    UnitPairArithmeticModel (QuadInt 1 nu) where
  d := 4*nu-1
  positive := by simpa [QuadInt.discriminant] using hd
  squarefree := hsq
  w := ⟨-1,2⟩
  square := by ext <;> simp <;> ring
  conjugate := starRingEnd (QuadInt 1 nu)
  conjugate_w := by ext <;> simp [starRingEnd_apply]
  negative_square := fun _ hm hs => nonpositive_integer_square_trace_one hm hs
  pell := by
    intro z r s hz hr hs
    rcases QuadInt.unit_pair_half_basis_pell hd z r s hz hr hs with h | h
    · exact Or.inl h
    · right
      obtain ⟨u,v,hv,hPell,hz⟩ := h
      refine ⟨u,v,hv,hPell,?_⟩
      rw [hz]
      ext <;> simp <;> ring







end D1Bound5
end


