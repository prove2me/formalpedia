-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.hom_ext_of_localRing_points
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:03:12.218197+00:00
-- url     : https://prove2.me/submissions/66e050ac-61ea-42cd-b1e7-76ac32249aaf

import Mathlib

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

private theorem flat_fromSpecStalk {X : Scheme.{0}} (x : X) :
    Flat (X.fromSpecStalk x) := by
  let U := (X.affineCover.f (X.affineCover.idx x)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange _
  have hx : x ∈ U := X.affineCover.covers x
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hx]
  dsimp only [IsAffineOpen.fromSpecStalk]
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    (X.presheaf.germ U x hx).hom.toAlgebra
  letI := hU.isLocalization_stalk ⟨x, hx⟩
  haveI : Flat (Spec.map (X.presheaf.germ U x hx)) := by
    rw [Flat.SpecMap_iff]
    change (algebraMap Γ(X, U) (X.presheaf.stalk x)).Flat
    rw [RingHom.flat_algebraMap_iff]
    exact IsLocalization.flat (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  infer_instance

/-- Scheme morphisms are determined on spectra of local rings. The coproduct
of the spectra of all source stalks is flat and surjective, hence an epimorphism.
This tests infinitesimal information as well as the underlying points. -/
theorem _root_.solution {X Y : Scheme.{0}} (u v : X ⟶ Y)
    (h : ∀ (K : Type) [CommRing K] [IsLocalRing K]
      (p : Spec (CommRingCat.of K) ⟶ X), p ≫ u = p ≫ v) : u = v := by
  letI (x : X) : IsLocalRing (X.presheaf.stalk x) :=
    X.toLocallyRingedSpace.isLocalRing x
  let A : X → Scheme.{0} := fun x => Spec (X.presheaf.stalk x)
  let f : ∀ x, A x ⟶ X := fun x => X.fromSpecStalk x
  haveI : ∀ x, Flat (f x) := fun x => flat_fromSpecStalk x
  haveI : Surjective (Sigma.desc f) := ⟨fun x =>
    ⟨Sigma.ι A x (IsLocalRing.closedPoint (X.presheaf.stalk x)), by
      change (Sigma.ι A x ≫ Sigma.desc f)
        (IsLocalRing.closedPoint (X.presheaf.stalk x)) = x
      rw [Sigma.ι_desc]
      exact Scheme.fromSpecStalk_closedPoint⟩⟩
  haveI : Epi (Sigma.desc f) := Flat.epi_of_flat_of_surjective _
  apply (cancel_epi (Sigma.desc f)).mp
  apply Sigma.hom_ext
  intro x
  simpa only [Sigma.ι_desc_assoc] using
    @h (X.presheaf.stalk x) inferInstance (X.toLocallyRingedSpace.isLocalRing x) (f x)

end AlgebraicGeometry.Scheme
