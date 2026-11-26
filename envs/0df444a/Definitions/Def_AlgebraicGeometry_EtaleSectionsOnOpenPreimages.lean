-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleSectionsOnOpenPreimages
-- name    : AlgebraicGeometry_EtaleSectionsOnOpenPreimages
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-26T02:58:55.149083+00:00
-- url     : https://prove2.me/theorems/40600cab-737a-516d-a733-4f50912e1270
-- title:
--   Sections of an étale inverse image on the preimage of an open
-- statement:
--   The degree-zero comparison for an open in an inverse image is natural in the original coefficients.
-- source:
--   Mayer–Vietoris and the finite model method for étale cohomology.

import Definitions.Def_AlgebraicGeometry_EtaleOverlapBoundary

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open PhilipponEtaleExtensionByZero (restrict)
open PhilipponEtaleMayerVietoris (overlapBoundary overlapBoundary_naturality overlapBoundary_surjective)
open PhilipponEtaleNeighborhoodRestriction (restrictionIso)
open PhilipponEtaleOpenCohomology (openComparison openComparison_map)
open PhilipponEtalePullbackComposition (pullbackCompIso)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)


namespace PhilipponEtaleClosedFiberOverlap

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

variable {S X : Scheme.{u}} (j : S ⟶ X) (W : X.Opens)

/-- Restricting an inverse image to the preimage of an open is the inverse
image of the restricted coefficient sheaf. -/
def restrictPullbackIso :
    pullbackSheaves j ⋙ restrict (j ⁻¹ᵁ W).ι ≅ restrict W.ι ⋙ pullbackSheaves (j ∣_ W) :=
  Functor.isoWhiskerLeft (pullbackSheaves j) (restrictionIso (j ⁻¹ᵁ W).ι) ≪≫
    pullbackCompIso j (j ⁻¹ᵁ W).ι ≪≫
    eqToIso (congrArg pullbackSheaves (morphismRestrict_ι j W).symm) ≪≫
    (pullbackCompIso W.ι (j ∣_ W)).symm ≪≫
    Functor.isoWhiskerRight (restrictionIso W.ι).symm (pullbackSheaves (j ∣_ W))

def preimageSectionsIso (O : S.Opens) (hO : O = j ⁻¹ᵁ W) (F : Ab X) :
    ((pullbackSheaves j).obj F).H' 0 (Scheme.Etale.mk O.ι) ≃+
      ((pullbackSheaves (j ∣_ W)).obj ((restrict W.ι).obj F)).H 0 := by
  subst O
  exact (openComparison (j ⁻¹ᵁ W).ι ((pullbackSheaves j).obj F) 0).trans
    (((Sheaf.functorH _ 0).mapIso ((restrictPullbackIso j W).app F)).addCommGroupIsoToAddEquiv)

private theorem naturality_apply {C D : Type*} [Category* C] [Category* D] {L R : C ⥤ D}
    (E : L ≅ R) (H : D ⥤ AddCommGrpCat.{u}) {F G : C} (a : F ⟶ G)
    (x : H.obj (L.obj F)) :
    H.map (E.hom.app G) (H.map (L.map a) x) = H.map (R.map a) (H.map (E.hom.app F) x) := by
  have h := congrArg H.map (E.hom.naturality a)
  rw [H.map_comp, H.map_comp] at h
  exact ConcreteCategory.congr_hom h x

theorem preimageSectionsIso_map (O : S.Opens) (hO : O = j ⁻¹ᵁ W)
    {F G : Ab X} (a : F ⟶ G)
    (t : ((pullbackSheaves j).obj F).H' 0 (Scheme.Etale.mk O.ι)) :
    preimageSectionsIso j W O hO G (t.comp (Ext.mk₀ ((pullbackSheaves j).map a)) rfl) =
      Sheaf.H.map ((pullbackSheaves (j ∣_ W)).map ((restrict W.ι).map a)) 0
        (preimageSectionsIso j W O hO F t) := by
  subst O
  let Z := (j ⁻¹ᵁ W).toScheme
  let E := restrictPullbackIso j W
  let L := pullbackSheaves j ⋙ restrict (j ⁻¹ᵁ W).ι
  let R := restrict W.ι ⋙ pullbackSheaves (j ∣_ W)
  let H := Sheaf.functorH Z.smallEtaleTopology 0
  let e (F : Ab X) := openComparison (j ⁻¹ᵁ W).ι ((pullbackSheaves j).obj F) 0
  change H.map (E.hom.app G) (e G (t.comp (Ext.mk₀ ((pullbackSheaves j).map a)) rfl)) =
    H.map (R.map a) (H.map (E.hom.app F) (e F t))
  rw [openComparison_map]
  exact naturality_apply (L := L) (R := R) E H a (e F t)

theorem vanishing_on_preimage (F : Ab X) (n : ℕ)
    (h : Subsingleton (((pullbackSheaves (j ∣_ W)).obj ((restrict W.ι).obj F)).H n)) :
    Subsingleton (((restrict (j ⁻¹ᵁ W).ι).obj ((pullbackSheaves j).obj F)).H n) := by
  let e := ((Sheaf.functorH _ n).mapIso ((restrictPullbackIso j W).app F)).addCommGroupIsoToAddEquiv
  exact ⟨fun a b => e.injective (h.elim (e a) (e b))⟩

end PhilipponEtaleClosedFiberOverlap

end

end


