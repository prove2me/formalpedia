-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Hom.map_stalkMap_maximalIdeal_eq_of_etale_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/60b08ec1-2c98-58eb-b754-34e3c0d6f650

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_map_stalkMap_maximalIdeal_eq_of_etale_restrict

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) (W : X.Opens) [AlgebraicGeometry.Etale (W.ι ≫ f)] (x : X) (hx : x ∈ W) :
    Ideal.map (f.stalkMap x).hom (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f.base x))) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  classical
  let x' : (W : Scheme.{u}) := ⟨x, hx⟩
  have hxW : W.ι.base x' = x := rfl

  have key : Ideal.map ((W.ι ≫ f).stalkMap x').hom (IsLocalRing.maximalIdeal (Y.presheaf.stalk ((W.ι ≫ f).base x'))) =
      IsLocalRing.maximalIdeal ((W : Scheme.{u}).presheaf.stalk x') := by
    algebraize [((W.ι ≫ f).stalkMap x').hom]
    have : IsLocalHom (algebraMap (Y.presheaf.stalk ((W.ι ≫ f).base x')) ((W : Scheme.{u}).presheaf.stalk x')) :=
      inferInstanceAs <| IsLocalHom ((W.ι ≫ f).stalkMap x').hom
    have : Algebra.EssFiniteType (Y.presheaf.stalk ((W.ι ≫ f).base x')) ((W : Scheme.{u}).presheaf.stalk x') := by
      rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
      exact LocallyOfFiniteType.stalkMap (W.ι ≫ f) x'
    have : Algebra.FormallyUnramified (Y.presheaf.stalk ((W.ι ≫ f).base x')) ((W : Scheme.{u}).presheaf.stalk x') := by
      rw [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra]
      exact FormallyUnramified.stalkMap (W.ι ≫ f) x'
    exact Algebra.FormallyUnramified.map_maximalIdeal

  simp only [Scheme.Hom.stalkMap_comp] at key
  change Ideal.map ((W.ι.stalkMap x').hom.comp (f.stalkMap x).hom) (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f.base x))) =
    IsLocalRing.maximalIdeal _ at key
  rw [← Ideal.map_map] at key

  haveI : IsIso (W.ι.stalkMap x') := inferInstance
  let E : X.presheaf.stalk x ≃+* (W : Scheme.{u}).presheaf.stalk x' := (asIso (W.ι.stalkMap x')).commRingCatIsoToRingEquiv
  have hcomp : (E.symm : (W : Scheme.{u}).presheaf.stalk x' →+* X.presheaf.stalk x).comp
      ((W.ι.stalkMap x').hom : X.presheaf.stalk x →+* (W : Scheme.{u}).presheaf.stalk x') = RingHom.id (X.presheaf.stalk x) :=
    RingHom.ext fun z => E.symm_apply_apply z
  have key2 := congrArg (Ideal.map (E.symm : (W : Scheme.{u}).presheaf.stalk x' →+* X.presheaf.stalk x)) key
  erw [Ideal.map_map, hcomp, Ideal.map_id] at key2
  haveI : IsLocalHom (E.symm : (W : Scheme.{u}).presheaf.stalk x' →+* X.presheaf.stalk x) :=
    ⟨fun a ha => by
      have h := ha.map E
      rwa [show E ((E.symm : (W : Scheme.{u}).presheaf.stalk x' →+* X.presheaf.stalk x) a) = a from E.apply_symm_apply a] at h⟩
  exact key2.trans (IsLocalRing.map_maximalIdeal_of_surjective
    (E.symm : (W : Scheme.{u}).presheaf.stalk x' →+* X.presheaf.stalk x) E.symm.surjective)

end S_AlgebraicGeometry_Scheme_Hom_map_stalkMap_maximalIdeal_eq_of_etale_restrict
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Hom_map_stalkMap_maximalIdeal_eq_of_etale_restrict (solution)
