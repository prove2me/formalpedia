-- Prove2me | solution 1 for AlgebraicGeometry.isReduced_of_smooth_over_field
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/a0ceed89-fb1d-5ade-9bbc-5388723cecd9

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.RingHom.LocallyStandardSmooth
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Flat.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isReduced_of_smooth_over_field

set_option autoImplicit false

universe u

open TensorProduct

namespace IsReducedOfSmoothFieldAux

theorem etale_isReduced (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    [Algebra.Etale K A] : IsReduced A := by
  haveI : Algebra.FormallyUnramified K A := inferInstance
  haveI : Algebra.EssFiniteType K A := inferInstance
  exact Algebra.FormallyUnramified.isReduced_of_field K A

theorem isStandardSmooth_isReduced_of_isDomain
    {R A : Type u} [CommRing R] [CommRing A] [IsDomain R] {φ : R →+* A}
    (hφ : φ.IsStandardSmooth) : IsReduced A := by
  obtain ⟨n, g, -, hg⟩ := hφ.exists_etale_mvPolynomial
  letI : Algebra (MvPolynomial (Fin n) R) A := g.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin n) R) A := hg.toAlgebra
  haveI : IsReduced
      (FractionRing (MvPolynomial (Fin n) R) ⊗[MvPolynomial (Fin n) R] A) :=
    IsReducedOfSmoothFieldAux.etale_isReduced (FractionRing (MvPolynomial (Fin n) R)) _
  exact isReduced_of_injective
    (Algebra.TensorProduct.includeRight :
      A →ₐ[MvPolynomial (Fin n) R]
        FractionRing (MvPolynomial (Fin n) R) ⊗[MvPolynomial (Fin n) R] A)
    (Algebra.TensorProduct.includeRight_injective
      (IsFractionRing.injective (MvPolynomial (Fin n) R)
        (FractionRing (MvPolynomial (Fin n) R))))

theorem smooth_isReduced_of_isDomain
    {R A : Type u} [CommRing R] [CommRing A] [IsDomain R] {φ : R →+* A}
    (hφ : φ.Smooth) : IsReduced A := by
  rw [RingHom.smooth_iff_locally_isStandardSmooth] at hφ
  obtain ⟨s, hs, H⟩ := hφ
  constructor
  intro x hx
  apply Localization.algebraMap_injective_of_span_eq_top s hs
  rw [map_zero]
  funext a
  haveI : IsReduced (Localization.Away a.1) :=
    IsReducedOfSmoothFieldAux.isStandardSmooth_isReduced_of_isDomain (H a.1 a.2)
  simpa using IsReduced.eq_zero _ (hx.map (algebraMap A (Localization.Away a.1)))

end IsReducedOfSmoothFieldAux

section SchemeLevel

open AlgebraicGeometry CategoryTheory

theorem solution {k : Type u} [Field k]
    {Z : Scheme.{u}} {g : Z ⟶ Spec (.of k)} (hg : Smooth g) : IsReduced Z := by
  haveI := hg
  haveI : ∀ i, IsReduced (Z.affineCover.X i) := by
    intro i
    haveI : IsDomain Γ(Spec (CommRingCat.of k), ⊤) :=
      Function.Injective.isDomain _
        (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.injective
    haveI : _root_.IsReduced ↑Γ(Z.affineCover.X i, ⊤) :=
      IsReducedOfSmoothFieldAux.smooth_isReduced_of_isDomain
        ((HasRingHomProperty.iff_of_isAffine (P := @Smooth)).mp
          (inferInstance : Smooth (Z.affineCover.f i ≫ g)))
    exact isReduced_of_isAffine_isReduced _
  exact IsReduced.of_openCover _ Z.affineCover

end SchemeLevel

#print axioms solution

end S_AlgebraicGeometry_isReduced_of_smooth_over_field
end P2MW
export P2MW.S_AlgebraicGeometry_isReduced_of_smooth_over_field (solution)
