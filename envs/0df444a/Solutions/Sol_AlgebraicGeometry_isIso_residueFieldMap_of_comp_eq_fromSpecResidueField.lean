-- Prove2me | solution 1 for AlgebraicGeometry.isIso_residueFieldMap_of_comp_eq_fromSpecResidueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/dd5e5603-2d4d-5792-9e43-1566ab140da0

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isIso_residueFieldMap_of_comp_eq_fromSpecResidueField

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem solution
    {X Y : Scheme.{0}} (f : X ⟶ Y) (y : Y) (u₀ : Spec (Y.residueField y) ⟶ X)
    (hu₀ : u₀ ≫ f = Y.fromSpecResidueField y) :
    IsIso (f.residueFieldMap (u₀.base (IsLocalRing.closedPoint (Y.residueField y)))) := by
  classical
  haveI i0 : IsLocalRing (IsLocalRing.ResidueField ↑(Y.presheaf.stalk y)) := inferInstanceAs (IsLocalRing ↑(Y.residueField y))
  have i1 : IsLocalHom (CommRingCat.Hom.hom (Scheme.stalkClosedPointTo u₀)) := Scheme.isLocalHom_stalkClosedPointTo u₀

  obtain ⟨b, hb⟩ : ∃ b : X.residueField (u₀.base (IsLocalRing.closedPoint (Y.residueField y))) ⟶ Y.residueField y,
      X.residue _ ≫ b = Scheme.stalkClosedPointTo u₀ :=
    ⟨@Scheme.descResidueField _ _ X _ (Scheme.stalkClosedPointTo u₀) i1, @Scheme.residue_descResidueField _ _ X _ _ i1⟩

  have h1 : Scheme.SpecToEquivOfField (Y.residueField y) Y (u₀ ≫ f) = ⟨y, 𝟙 _⟩ := by
    rw [hu₀, ← (Scheme.SpecToEquivOfField (Y.residueField y) Y).apply_symm_apply ⟨y, 𝟙 _⟩]
    congr 1
    simp [Scheme.SpecToEquivOfField]
    exact (Category.id_comp _).symm
  rw [Scheme.SpecToEquivOfField_eq_iff] at h1
  obtain ⟨e, he⟩ := h1
  simp only [Scheme.SpecToEquivOfField, Equiv.coe_fn_mk, Category.comp_id] at he e

  have i2 : IsLocalHom (CommRingCat.Hom.hom (Scheme.stalkClosedPointTo (u₀ ≫ f))) := Scheme.isLocalHom_stalkClosedPointTo (u₀ ≫ f)
  have h3 : Y.residue _ ≫ @Scheme.descResidueField _ _ Y _ (Scheme.stalkClosedPointTo (u₀ ≫ f)) i2 = Scheme.stalkClosedPointTo (u₀ ≫ f) :=
    @Scheme.residue_descResidueField _ _ Y _ _ i2
  have h4 : Y.residue (f.base (u₀.base (IsLocalRing.closedPoint (Y.residueField y)))) ≫
      f.residueFieldMap (u₀.base (IsLocalRing.closedPoint (Y.residueField y))) ≫ b =
        f.stalkMap (u₀.base (IsLocalRing.closedPoint (Y.residueField y))) ≫ Scheme.stalkClosedPointTo u₀ := by
    rw [Scheme.residue_residueFieldMap_assoc, hb]
  have h5 : Y.residue (f.base (u₀.base (IsLocalRing.closedPoint (Y.residueField y)))) ≫
      f.residueFieldMap (u₀.base (IsLocalRing.closedPoint (Y.residueField y))) ≫ b =
        Y.residue (f.base (u₀.base (IsLocalRing.closedPoint (Y.residueField y)))) ≫ @Scheme.descResidueField _ _ Y _ (Scheme.stalkClosedPointTo (u₀ ≫ f)) i2 :=
    h4.trans ((Scheme.stalkClosedPointTo_comp u₀ f).symm.trans h3.symm)
  have h2 : f.residueFieldMap (u₀.base (IsLocalRing.closedPoint (Y.residueField y))) ≫ b = (Y.residueFieldCongr e).hom := by
    rw [← he]
    haveI : Epi (Y.residue (f.base (u₀.base (IsLocalRing.closedPoint (Y.residueField y))))) :=
      ConcreteCategory.epi_of_surjective _ (Y.residue_surjective _)
    exact (cancel_epi (Y.residue (f.base (u₀.base (IsLocalRing.closedPoint (Y.residueField y)))))).mp h5

  rw [ConcreteCategory.isIso_iff_bijective]
  have hcomp : Function.Bijective ((f.residueFieldMap (u₀.base (IsLocalRing.closedPoint (Y.residueField y))) ≫ b)) := by
    rw [h2]; exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  have hbinj : Function.Injective b := b.hom.injective
  refine ⟨Function.Injective.of_comp (f := ⇑(ConcreteCategory.hom b)) ?_, fun z => ?_⟩
  · exact hcomp.1
  · obtain ⟨w, hw⟩ := hcomp.2 (b z)
    exact ⟨w, hbinj hw⟩

end S_AlgebraicGeometry_isIso_residueFieldMap_of_comp_eq_fromSpecResidueField
end P2MW
export P2MW.S_AlgebraicGeometry_isIso_residueFieldMap_of_comp_eq_fromSpecResidueField (solution)
