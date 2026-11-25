-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_etale_H_zero_preimage_of_filtered_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-25T20:08:47.4907+00:00
-- url     : https://prove2.me/submissions/d68b01f6-9566-4fdb-b9c7-c4489bde7f53

import Definitions.Def_AlgebraicGeometry_EtaleAffineLimitSectionRepresentatives
import Definitions.Def_AlgebraicGeometry_EtaleConstantDiagramSheafColimit

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleAcyclicCohomology (globalSections globalSectionsIso
  globalSectionsIso_hom_app_eq_map isTerminal)
open PhilipponEtaleConstantDiagramColimit (cocone coneIsLimit isColimitCocone)
open PhilipponEtaleConstantDiagramSystem (ofSheafDiagram unit)
open PhilipponEtaleLimitSectionProjections (stageSections)

namespace PhilipponEtaleFilteredDegreeZero

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

private theorem sections_unit {I : Type u} [Category.{u} I] (i : I) (X : Scheme.{u})
    (F : Ab X) : (globalSectionsIso (𝟙 X)).hom.app F =
      (globalSections X).map ((unit X i).hom.app F) := by
  let D := (Functor.const I).obj X
  let t := Scheme.Etale.mk (𝟙 X)
  let a := (PhilipponEtaleDirectImageSystem.unitChart D i).inv.app t
  exact globalSectionsIso_hom_app_eq_map (𝟙 X) F a

private theorem exists_preimage_op {I : Type u} [Category.{u} I] [IsCofiltered I]
    (X : Scheme.{u}) [IsAffine X] (F : Iᵒᵖ ⥤ Ab X) (d : Cocone F) (hd : IsColimit d)
    (x : d.pt.H 0) : ∃ (j : Iᵒᵖ) (y : (F.obj j).H 0), Sheaf.H.map (d.ι.app j) 0 y = x := by
  let : ∀ i, IsAffine (((Functor.const I).obj X).obj i) := fun _ => inferInstanceAs (IsAffine X)
  let c := constCone I X
  let hc := coneIsLimit (I := I) X
  let S := ofSheafDiagram X F
  let hi := Classical.choice (IsCofiltered.nonempty (C := I))
  let P := globalSections X
  let e := (isColimitCocone X F).coconePointUniqueUpToIso hd
  let eP := P.mapIso e
  let a (G : Ab X) := Sheaf.H.equiv₀ G (isTerminal X)
  obtain ⟨j, z, hz⟩ := PhilipponEtaleLimitSectionSurjectivity.exists_stage_section
    c hc hi S (eP.inv (a d.pt x))
  have hj : stageSections c hc S j = P.map ((cocone X F).ι.app (op j)) := by
    change P.map (PhilipponEtaleLimitCanonical.fromStage c hc S j) ≫
      (globalSectionsIso (𝟙 X)).hom.app _ =
      P.map (PhilipponEtaleLimitCanonical.fromStage c hc S j ≫ (unit X j).hom.app _)
    rw [sections_unit j, Functor.map_comp]
  have he := (isColimitCocone X F).fac d (op j)
  refine ⟨op j, (a _).symm z, (a d.pt).injective ?_⟩
  rw [show (a d.pt) (Sheaf.H.map (d.ι.app (op j)) 0 ((a _).symm z)) =
      P.map (d.ι.app (op j)) ((a _) ((a _).symm z)) from
    (Sheaf.H.equiv₀_naturality (isTerminal X) (d.ι.app (op j)) ((a _).symm z)).symm,
    AddEquiv.apply_symm_apply, ← he, Functor.map_comp, ConcreteCategory.comp_apply, ← hj]
  change eP.hom (stageSections c hc S j z) = a d.pt x
  exact (congrArg (fun t => eP.hom t) hz).trans
    (ConcreteCategory.congr_hom eP.inv_hom_id (a d.pt x))

/-- Degree-zero cohomology classes over an affine scheme lift to a term
of any filtered colimit of coefficient sheaves. -/
theorem exists_preimage {J : Type u} [Category.{u} J] [IsFiltered J]
    (X : Scheme.{u}) [IsAffine X] (F : J ⥤ Ab X) (d : Cocone F) (hd : IsColimit d)
    (x : d.pt.H 0) : ∃ (j : J) (y : (F.obj j).H 0), Sheaf.H.map (d.ι.app j) 0 y = x := by
  let E := (opOpEquivalence J).functor
  obtain ⟨j, y, hy⟩ := exists_preimage_op (I := Jᵒᵖ) X (E ⋙ F)
    (d.whisker E) ((Functor.Final.isColimitWhiskerEquiv E d).symm hd) x
  exact ⟨E.obj j, y, hy⟩

end PhilipponEtaleFilteredDegreeZero

end

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    {J : Type u} [Category.{u} J] [IsFiltered J]
    (X : Scheme.{u}) [IsAffine X] (F : J ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (d : Cocone F) (hd : IsColimit d) (x : d.pt.H 0) :
    ∃ (j : J) (y : (F.obj j).H 0), Sheaf.H.map (d.ι.app j) 0 y = x := by
  exact
    PhilipponEtaleFilteredDegreeZero.exists_preimage X F d hd x

end

end
