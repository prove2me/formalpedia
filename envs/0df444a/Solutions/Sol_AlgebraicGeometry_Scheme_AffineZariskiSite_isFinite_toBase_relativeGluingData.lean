-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.AffineZariskiSite.isFinite_toBase_relativeGluingData
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/eaa9fc5c-4f6b-5f13-8be8-73348c8d2c2b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_AffineZariskiSite_isFinite_toBase_relativeGluingData

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace FormalGAGAFiniteRelSpecAux

open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.AffineZariskiSite

variable {X : Scheme.{u}} {F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}}
    {α : (AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F} (H : α.Coequifibered)

scoped instance instIsLocallyDirected :
    ((relativeGluingData H).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

set_option backward.isDefEq.respectTransparency false in
theorem ι_toBase (U : X.AffineZariskiSite) :
    (relativeGluingData H).cover.f U ≫ (relativeGluingData H).toBase =
      Spec.map (α.app (op U)) ≫ U.2.fromSpec :=
  colimit.ι_desc _ _

theorem toBase_preimage (U : X.AffineZariskiSite) :
    (relativeGluingData H).toBase ⁻¹ᵁ U.1 = ((relativeGluingData H).cover.f U).opensRange := by
  have h__af := (relativeGluingData H).toBase_preimage_eq_opensRange_ι U
  simp at h__af
  exact h__af

end FormalGAGAFiniteRelSpecAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_AffineZariskiSite_isFinite_toBase_relativeGluingData.FormalGAGAFiniteRelSpecAux"

open FormalGAGAFiniteRelSpecAux AlgebraicGeometry.Scheme in
set_option backward.isDefEq.respectTransparency false in
theorem solution
    {X : Scheme.{u}} {F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}}
    {α : (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F} (H : α.Coequifibered)
    (hfin : ∀ U : X.AffineZariskiSite, (α.app (op U)).hom.Finite) :
    IsFinite (Scheme.AffineZariskiSite.relativeGluingData H).toBase := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsFinite) _ (iSup_affineOpens_eq_top _)]
  intro U
  let U' : X.AffineZariskiSite := ⟨U.1, U.2⟩
  let e := IsOpenImmersion.isoOfRangeEq ((AffineZariskiSite.relativeGluingData H).toBase ⁻¹ᵁ U).ι
    ((AffineZariskiSite.relativeGluingData H).cover.f U')
      (by simpa using congr($(toBase_preimage H U').1))
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsFinite e.inv,
    ← MorphismProperty.cancel_right_of_respectsIso @IsFinite _ U.2.isoSpec.hom]
  convert! (IsFinite.SpecMap_iff _).mpr (hfin U')
  rw [← cancel_mono U.2.fromSpec]
  have h := ι_toBase H U'
  simp only [Cover.RelativeGluingData.cover_f] at h
  simp [IsAffineOpen.isoSpec_hom, e, h, U']

end S_AlgebraicGeometry_Scheme_AffineZariskiSite_isFinite_toBase_relativeGluingData
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_AffineZariskiSite_isFinite_toBase_relativeGluingData (solution)
