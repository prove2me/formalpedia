-- Prove2me | solution 1 for AlgebraicGeometry.geometricallyIrreducible_of_irreducibleSpace_pullback_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/519a8463-de15-5bfe-913c-4b99b43f5d34

import Mathlib
import Theorems.Thm_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_geometricallyIrreducible_of_irreducibleSpace_pullback_of_isAlgClosed

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

namespace H2a2N2

theorem surjective_specMap_of_field {L M : Type u} [Field L] [Field M] (i : L →+* M) :
    Surjective (Spec.map (CommRingCat.ofHom i)) :=
  ⟨fun _ => ⟨IsLocalRing.closedPoint M, Subsingleton.elim _ _⟩⟩

theorem main {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
    (k : Type u) [Field k] [Algebra K k] [IsAlgClosed k]
    [IrreducibleSpace ↑(pullback f (Spec.map (CommRingCat.ofHom (algebraMap K k))))] :
    GeometricallyIrreducible f := by

  haveI hk : GeometricallyIrreducible (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K k)))) :=
    AlgebraicGeometry.GeometricallyIrreducible.of_irreducibleSpace_of_isAlgClosed _
  refine ⟨fun L _ y Z fst snd h => ?_⟩
  obtain ⟨φ, rfl⟩ := Spec.map_surjective y
  letI : Algebra K L := φ.hom.toAlgebra

  haveI : Nontrivial (L ⊗[K] k) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain K L k
      (algebraMap K L).injective (algebraMap K k).injective
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (L ⊗[K] k)
  letI : Field ((L ⊗[K] k) ⧸ m) := Ideal.Quotient.field m
  let iL : L →+* (L ⊗[K] k) ⧸ m := (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeLeftRingHom
  let ik : k →+* (L ⊗[K] k) ⧸ m := (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight (R := K) (A := L)).toRingHom
  have hcompat : iL.comp φ.hom = ik.comp (algebraMap K k) := by
    ext a
    show Ideal.Quotient.mk m (algebraMap K L a ⊗ₜ[K] (1 : k)) = Ideal.Quotient.mk m ((1 : L) ⊗ₜ[K] algebraMap K k a)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  let yL : Spec (CommRingCat.of ((L ⊗[K] k) ⧸ m)) ⟶ Spec (CommRingCat.of L) := Spec.map (CommRingCat.ofHom iL)
  let yk : Spec (CommRingCat.of ((L ⊗[K] k) ⧸ m)) ⟶ Spec (CommRingCat.of k) := Spec.map (CommRingCat.ofHom ik)
  have hy : yL ≫ Spec.map φ = yk ≫ Spec.map (CommRingCat.ofHom (algebraMap K k)) := by
    show Spec.map (CommRingCat.ofHom iL) ≫ Spec.map φ = Spec.map (CommRingCat.ofHom ik) ≫ Spec.map (CommRingCat.ofHom (algebraMap K k))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_hom φ, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hcompat]

  let fk := pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K k)))
  haveI : IrreducibleSpace ↥(pullback fk yk) :=
    hk.geometrically_irreducibleSpace yk _ _ (IsPullback.of_hasPullback fk yk)

  have houter : IsPullback (pullback.fst fk yk ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K k))))
      (pullback.snd fk yk) f (yL ≫ Spec.map φ) := by
    rw [hy]
    exact (IsPullback.of_hasPullback fk yk).paste_horiz (IsPullback.of_hasPullback f _)
  let t : pullback fk yk ⟶ Z := h.lift (pullback.fst fk yk ≫ pullback.fst f _) (pullback.snd fk yk ≫ yL)
    (by simpa only [Category.assoc] using houter.w)
  have ht₁ : t ≫ fst = pullback.fst fk yk ≫ pullback.fst f _ := h.lift_fst _ _ _
  have ht₂ : t ≫ snd = pullback.snd fk yk ≫ yL := h.lift_snd _ _ _
  have hsq : IsPullback t (pullback.snd fk yk) snd yL :=
    IsPullback.of_right (by rw [ht₁]; exact houter) ht₂ h
  haveI := surjective_specMap_of_field iL
  haveI : Surjective t := MorphismProperty.of_isPullback (P := @Surjective) hsq.flip (inferInstance : Surjective yL)
  exact t.surjective.irreducibleSpace t.continuous

end H2a2N2

theorem solution
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
    (k : Type u) [Field k] [Algebra K k] [IsAlgClosed k]
    [IrreducibleSpace ↑(pullback f (Spec.map (CommRingCat.ofHom (algebraMap K k))))] :
    GeometricallyIrreducible f :=
  H2a2N2.main f k

end S_AlgebraicGeometry_geometricallyIrreducible_of_irreducibleSpace_pullback_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicGeometry_geometricallyIrreducible_of_irreducibleSpace_pullback_of_isAlgClosed (solution)
