-- Prove2me | solution 1 for AlgebraicGeometry.mem_smoothLocus_iff_formallySmooth_of_ringEquiv_stalk
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/2b3e9884-6bc9-563d-a7de-78ef78911402

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_mem_smoothLocus_iff_formallySmooth_of_ringEquiv_stalk

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem solution
    {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation f]
    (x : X) {S : Type} [CommRing S] [Algebra R S] (e : X.presheaf.stalk x ≃+* S)
    (he : ∀ r : R, e ((X.presheaf.germ ⊤ x trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) =
      algebraMap R S r) :
    x ∈ f.smoothLocus ↔ Algebra.FormallySmooth R S := by
  classical
  set p : PrimeSpectrum R := f.base x with hp

  letI algRp : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk p) := StructureSheaf.stalkAlgebra R p
  haveI : IsLocalization.AtPrime ((Spec (CommRingCat.of R)).presheaf.stalk p) p.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R p
  letI algT : Algebra ((Spec (CommRingCat.of R)).presheaf.stalk p) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra

  let c : R →+* X.presheaf.stalk x :=
    (X.presheaf.germ ⊤ x trivial).hom.comp (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
  letI algRT : Algebra R (X.presheaf.stalk x) := c.toAlgebra
  have hchain : ∀ r : R, (f.stalkMap x).hom (algebraMap R ((Spec (CommRingCat.of R)).presheaf.stalk p) r) = c r := by
    intro r
    have h1 : algebraMap R ((Spec (CommRingCat.of R)).presheaf.stalk p) r =
        ((Spec (CommRingCat.of R)).presheaf.germ ⊤ (f.base x) trivial).hom
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := rfl
    rw [h1, Scheme.Hom.germ_stalkMap_apply]
    rfl
  haveI : IsScalarTower R ((Spec (CommRingCat.of R)).presheaf.stalk p) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq fun r => (hchain r).symm

  letI algS' : Algebra R S := inferInstance
  let eA : X.presheaf.stalk x ≃ₐ[R] S := AlgEquiv.ofRingEquiv (f := e) (fun r => he r)
  have key : (f.stalkMap x).hom.FormallySmooth ↔
      Algebra.FormallySmooth ((Spec (CommRingCat.of R)).presheaf.stalk p) (X.presheaf.stalk x) :=
    RingHom.formallySmooth_algebraMap
  rw [Scheme.Hom.mem_smoothLocus, key]
  constructor
  · intro h
    haveI := h
    haveI : Algebra.FormallySmooth R ((Spec (CommRingCat.of R)).presheaf.stalk p) :=
      Algebra.FormallySmooth.of_isLocalization p.asIdeal.primeCompl
    haveI : Algebra.FormallySmooth R (X.presheaf.stalk x) :=
      Algebra.FormallySmooth.comp R ((Spec (CommRingCat.of R)).presheaf.stalk p) (X.presheaf.stalk x)
    exact Algebra.FormallySmooth.of_equiv eA
  · intro h
    haveI := h
    haveI : Algebra.FormallySmooth R (X.presheaf.stalk x) := Algebra.FormallySmooth.of_equiv eA.symm
    exact Algebra.FormallySmooth.localization_base p.asIdeal.primeCompl

end S_AlgebraicGeometry_mem_smoothLocus_iff_formallySmooth_of_ringEquiv_stalk
end P2MW
export P2MW.S_AlgebraicGeometry_mem_smoothLocus_iff_formallySmooth_of_ringEquiv_stalk (solution)
