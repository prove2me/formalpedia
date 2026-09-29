-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Hom.eq_of_forall_comp_eq_of_dense_of_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/6c24e80e-2840-5931-9c30-6fc0b10c2694

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_eq_of_forall_comp_eq_of_dense_of_isReduced

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace DenseSetAgree

theorem epi_specMap_of_field {κ k : Type u} [Field κ] [Field k] (φ : CommRingCat.of κ ⟶ CommRingCat.of k) :
    Epi (Spec.map φ) := by
  haveI : Flat (Spec.map φ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    letI : Algebra κ k := φ.hom.toAlgebra
    show Module.Flat κ k
    infer_instance
  haveI : Surjective (Spec.map φ) := ⟨fun p => ⟨IsLocalRing.closedPoint k, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

end DenseSetAgree

theorem solution
    {X Y S : Scheme.{u}} [IsReduced X]
    (F G : X ⟶ Y) (i : Y ⟶ S) [IsSeparated i] (hFG : F ≫ i = G ≫ i)
    (D : Set ↥X) (hD : Dense D)
    (h : ∀ x ∈ D, ∃ (k : Type u) (_ : Field k) (y : Spec (CommRingCat.of k) ⟶ X),
      x ∈ Set.range y.base ∧ y ≫ F = y ≫ G) :
    F = G := by
  refine AlgebraicGeometry.ext_of_fromSpecResidueField_eq F G i D hD (fun x hx => ?_) hFG
  obtain ⟨k, _, y, ⟨p, rfl⟩, hy⟩ := h x hx
  obtain rfl : p = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  haveI := DenseSetAgree.epi_specMap_of_field (X.descResidueField (Scheme.stalkClosedPointTo y))
  rw [← cancel_epi (Spec.map (X.descResidueField (Scheme.stalkClosedPointTo y))), ← Category.assoc, ← Category.assoc,
    X.descResidueField_stalkClosedPointTo_fromSpecResidueField k y]
  exact hy

end S_AlgebraicGeometry_Scheme_Hom_eq_of_forall_comp_eq_of_dense_of_isReduced
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Hom_eq_of_forall_comp_eq_of_dense_of_isReduced (solution)
