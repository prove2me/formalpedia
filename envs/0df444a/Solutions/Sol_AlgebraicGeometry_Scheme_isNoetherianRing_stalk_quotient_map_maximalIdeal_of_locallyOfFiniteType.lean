-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.isNoetherianRing_stalk_quotient_map_maximalIdeal_of_locallyOfFiniteType
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/64e27a18-6c0e-523f-bf92-ef249adcc515

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_isNoetherianRing_stalk_quotient_map_maximalIdeal_of_locallyOfFiniteType

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace FibreNoethAux

theorem isNoetherianRing_of_essFiniteType (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] [IsNoetherianRing R] : IsNoetherianRing S := by
  have h : IsNoetherianRing (Algebra.EssFiniteType.subalgebra R S) :=
    Algebra.FiniteType.isNoetherianRing R _
  exact IsLocalization.isNoetherianRing (Algebra.EssFiniteType.submonoid R S) S h

theorem essFiniteType_toStalk (A : Type) [CommRing A] (p : PrimeSpectrum A) :
    (StructureSheaf.toStalk A p).hom.EssFiniteType := by
  change (algebraMap A ((Spec.structureSheaf A).presheaf.stalk p)).EssFiniteType
  rw [RingHom.essFiniteType_algebraMap]
  exact Algebra.EssFiniteType.of_isLocalization _ p.asIdeal.primeCompl

theorem const_eq_comp (A : Type) [CommRing A]
    (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) (x : X) :
    (X.presheaf.germ ⊤ x trivial).hom.comp (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) =
      (f.stalkMap x).hom.comp (StructureSheaf.toStalk A (f.base x)).hom := by
  have h1 : (Spec (CommRingCat.of A)).presheaf.germ ⊤ (f.base x) trivial ≫ f.stalkMap x =
      f.appTop ≫ X.presheaf.germ ⊤ x trivial :=
    Scheme.Hom.germ_stalkMap f ⊤ x trivial
  have h2 : (X.presheaf.germ ⊤ x trivial).hom.comp (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) =
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial).hom := by
    simp only [CommRingCat.hom_comp, RingHom.comp_assoc]
  rw [h2, ← h1]
  rfl

theorem essFiniteType_const (A : Type) [CommRing A]
    (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) [LocallyOfFiniteType f] (x : X) :
    ((X.presheaf.germ ⊤ x trivial).hom.comp
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).EssFiniteType := by
  rw [const_eq_comp]
  exact RingHom.EssFiniteType.comp (essFiniteType_toStalk A (f.base x)) (LocallyOfFiniteType.stalkMap f x)

end FibreNoethAux

theorem solution
    (A : Type) [CommRing A] [IsLocalRing A]
    (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) [LocallyOfFiniteType f]
    (x : X) (hx : f.base x = closedPoint A) :
    IsNoetherianRing
      ((X.presheaf.stalk x) ⧸ Ideal.map
        ((X.presheaf.germ ⊤ x trivial).hom.comp (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
        (maximalIdeal A)) := by
  have hc := FibreNoethAux.essFiniteType_const A X f x
  letI alg : Algebra A (X.presheaf.stalk x) :=
    ((X.presheaf.germ ⊤ x trivial).hom.comp
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).toAlgebra
  haveI hE : Algebra.EssFiniteType A (X.presheaf.stalk x) := hc
  have hq := Algebra.EssFiniteType.quotient_map (R := A) (S := X.presheaf.stalk x) (maximalIdeal A)
  letI fld : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field (maximalIdeal A)
  haveI : IsNoetherianRing (A ⧸ maximalIdeal A) := inferInstance
  have hN := @FibreNoethAux.isNoetherianRing_of_essFiniteType (A ⧸ maximalIdeal A)
    ((X.presheaf.stalk x) ⧸ (maximalIdeal A).map (algebraMap A (X.presheaf.stalk x))) _ _ _ hq inferInstance
  exact hN

end S_AlgebraicGeometry_Scheme_isNoetherianRing_stalk_quotient_map_maximalIdeal_of_locallyOfFiniteType
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_isNoetherianRing_stalk_quotient_map_maximalIdeal_of_locallyOfFiniteType (solution)
