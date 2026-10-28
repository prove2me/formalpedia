-- Prove2me | solution 1 for AlgebraicGeometry.exists_finite_extension_lift_of_surjective_locallyOfFiniteType
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-26T18:54:05.210994+00:00
-- url     : https://prove2.me/submissions/9ce0ef9a-3261-4342-91a6-6c5854e633e5

import Mathlib
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 10000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
namespace PhilipponFiniteMarkedPoints
lemma finite_residueField_of_closedPoint
    {K : Type u} [Field K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    letI := (Spec.preimage (X.fromSpecResidueField x ≫ π)).hom.toAlgebra
    FiniteDimensional K (X.residueField x) := by
  letI := (Spec.preimage (X.fromSpecResidueField x ≫ π)).hom.toAlgebra
  haveI : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  haveI : IsFinite (X.fromSpecResidueField x ≫ π) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  have h := (IsFinite.SpecMap_iff (Spec.preimage (X.fromSpecResidueField x ≫ π))).mp
    (by rw [Spec.map_preimage]; infer_instance)
  exact h


end PhilipponFiniteMarkedPoints


set_option autoImplicit false
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 10000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace PhilipponFiniteParameterLift

theorem exists_finite_extension_lift
    (K : Type u) [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Surjective f] [LocallyOfFiniteType f]
    (y : Spec (.of K) ⟶ Y) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (x : Spec (.of L) ⟶ X),
      x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ y := by
  classical
  let P : Scheme.{u} := pullback f y
  let p : P ⟶ Spec (.of K) := pullback.snd f y
  haveI : Surjective p := MorphismProperty.pullback_snd f y inferInstance
  haveI : LocallyOfFiniteType p := MorphismProperty.pullback_snd f y inferInstance
  haveI : Nonempty P := by
    obtain ⟨z, _⟩ := (inferInstance : Surjective p).surj (IsLocalRing.closedPoint K)
    exact ⟨z⟩
  haveI : JacobsonSpace P := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨z, _, hz⟩ := nonempty_inter_closedPoints
    (Set.univ_nonempty : (Set.univ : Set P).Nonempty) isOpen_univ.isLocallyClosed
  let L := P.residueField z
  let r := Spec.preimage (P.fromSpecResidueField z ≫ p)
  letI : Algebra K L := r.hom.toAlgebra
  have hfin : FiniteDimensional K L :=
    PhilipponFiniteMarkedPoints.finite_residueField_of_closedPoint p z hz
  let x : Spec (.of L) ⟶ X := P.fromSpecResidueField z ≫ pullback.fst f y
  refine ⟨L, inferInstance, inferInstance, hfin, x, ?_⟩
  dsimp only [x]
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  congr 1
  exact (Spec.map_preimage (P.fromSpecResidueField z ≫ p)).symm

end PhilipponFiniteParameterLift


theorem solution
    (K : Type u) [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Surjective f] [LocallyOfFiniteType f]
    (y : Spec (.of K) ⟶ Y) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (x : Spec (.of L) ⟶ X),
      x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ y := by
  exact PhilipponFiniteParameterLift.exists_finite_extension_lift K f y
