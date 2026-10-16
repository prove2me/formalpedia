-- Prove2me | Definitions.Def_Esgk_IrreduciblePlaneFunctionField
-- name    : Esgk_IrreduciblePlaneFunctionField
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:45:21.760428+00:00
-- url     : https://prove2.me/theorems/f41b490a-dbb5-4c34-973e-1c83146714e2
-- title:
--   Function field attached to an irreducible plane polynomial
-- statement:
--   This packages an irreducible plane polynomial with its quotient coordinate ring, fraction field, coordinate classes, and generation of those rings and fields by the coordinate functions.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_SelfCurveTwoAnchorFunctionField
import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

 
structure IrreduciblePlanePolynomial (F : Type*) [Field F] where
  polynomial : MvPolynomial (Fin 2) F
  irreducible : Irreducible polynomial

namespace IrreduciblePlanePolynomial

variable {F : Type*} [Field F]

 
abbrev CoordinateRing (C : IrreduciblePlanePolynomial F) :=
  MvPolynomial (Fin 2) F ⧸
    Ideal.span ({C.polynomial} : Set (MvPolynomial (Fin 2) F))

 
instance (C : IrreduciblePlanePolynomial F) : IsDomain C.CoordinateRing := by
  letI : (Ideal.span
      ({C.polynomial} : Set (MvPolynomial (Fin 2) F))).IsPrime :=
    (Ideal.span_singleton_prime C.irreducible.ne_zero).2
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp C.irreducible)
  exact Ideal.Quotient.isDomain _

 
abbrev FunctionField (C : IrreduciblePlanePolynomial F) :=
  FractionRing C.CoordinateRing

 
def coordinateClass (C : IrreduciblePlanePolynomial F) (i : Fin 2) :
    C.CoordinateRing :=
  Ideal.Quotient.mk _ (MvPolynomial.X i)

 
def coordinate (C : IrreduciblePlanePolynomial F) (i : Fin 2) :
    C.FunctionField :=
  algebraMap C.CoordinateRing C.FunctionField (C.coordinateClass i)


theorem adjoin_coordinateClass_range_eq_top
    (C : IrreduciblePlanePolynomial F) :
    Algebra.adjoin F (Set.range C.coordinateClass) = ⊤ := by
  let q : MvPolynomial (Fin 2) F →ₐ[F] C.CoordinateRing :=
    Ideal.Quotient.mkₐ F
      (Ideal.span ({C.polynomial} : Set (MvPolynomial (Fin 2) F)))
  have hq : q.range = (⊤ : Subalgebra F C.CoordinateRing) :=
    (AlgHom.range_eq_top q).2 (Ideal.Quotient.mkₐ_surjective F _)
  calc
    Algebra.adjoin F (Set.range C.coordinateClass) =
        Algebra.adjoin F
          (q '' Set.range
            (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) F)) := by
      congr 1
      ext z
      simp [coordinateClass, q]
    _ = (Algebra.adjoin F
          (Set.range
            (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) F))).map q := by
      rw [AlgHom.map_adjoin]
    _ = (⊤ : Subalgebra F (MvPolynomial (Fin 2) F)).map q := by
      rw [MvPolynomial.adjoin_range_X]
    _ = q.range := Algebra.map_top q
    _ = ⊤ := hq


theorem adjoin_coordinate_range_eq_top
    (C : IrreduciblePlanePolynomial F) :
    IntermediateField.adjoin F (Set.range C.coordinate) = ⊤ := by
  let A := C.CoordinateRing
  let K := C.FunctionField
  let g : A →ₐ[F] K := IsScalarTower.toAlgHom F A K
  have hg : g.range = Algebra.adjoin F (Set.range C.coordinate) := by
    calc
      g.range = (⊤ : Subalgebra F A).map g := (Algebra.map_top g).symm
      _ = (Algebra.adjoin F (Set.range C.coordinateClass)).map g := by
        rw [C.adjoin_coordinateClass_range_eq_top]
      _ = Algebra.adjoin F (g '' Set.range C.coordinateClass) :=
        AlgHom.map_adjoin g _
      _ = Algebra.adjoin F (Set.range C.coordinate) := by
        congr 1
        ext z
        simp [coordinate, g, A, K]
  have hfield := IsFractionRing.algHom_fieldRange_eq_of_comp_eq_of_range_eq
    (F := F) (A := A) (K := K) (L := K)
    (g := g) (f := AlgHom.id F K)
    (show RingHom.comp (RingHom.id K) (algebraMap A K) = algebraMap A K by
      exact RingHom.id_comp _)
    hg
  rw [← hfield]
  exact AlgHom.fieldRange_eq_top.mpr Function.surjective_id

theorem bundle_Esgk_IrreduciblePlaneFunctionField_coordinate_range_eq_pair
    (C : IrreduciblePlanePolynomial F) :
    Set.range C.coordinate = {C.coordinate 0, C.coordinate 1} := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hz
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with h | h
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩

 
theorem adjoin_coordinates_eq_top (C : IrreduciblePlanePolynomial F) :
    IntermediateField.adjoin F {C.coordinate 0, C.coordinate 1} = ⊤ := by
  rw [← C.bundle_Esgk_IrreduciblePlaneFunctionField_coordinate_range_eq_pair]
  exact C.adjoin_coordinate_range_eq_top

variable [CharZero F]


theorem exists_twoAnchorReflection
    (C : IrreduciblePlanePolynomial F) {r : F} (hr : r ≠ 0)
    (hy : C.coordinate 1 ∉
      Esgk.twoAnchorDistanceField (C.coordinate 0) (C.coordinate 1) r) :
    ∃ σ : C.FunctionField ≃ₐ[
        Esgk.twoAnchorDistanceField (C.coordinate 0) (C.coordinate 1) r]
        C.FunctionField,
      σ ≠ 1 ∧ σ (C.coordinate 0) = C.coordinate 0 ∧
        σ (C.coordinate 1) = -(C.coordinate 1) ∧ ∀ z, σ (σ z) = z :=
  Esgk.exists_twoAnchorReflectionAlgEquiv
    (C.coordinate 0) (C.coordinate 1) hr C.adjoin_coordinates_eq_top hy

end IrreduciblePlanePolynomial

end Esgk


