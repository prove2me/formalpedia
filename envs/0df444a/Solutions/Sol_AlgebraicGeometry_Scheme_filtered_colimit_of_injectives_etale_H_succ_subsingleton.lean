-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.filtered_colimit_of_injectives_etale_H_succ_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-25T20:01:45.998634+00:00
-- url     : https://prove2.me/submissions/4dd6f35d-68ce-4422-b9cc-2ca836d5a5f6

import Definitions.Def_AlgebraicGeometry_EtaleAffineLimitAcyclicity
import Definitions.Def_AlgebraicGeometry_EtaleConstantDiagramSheafColimit

noncomputable section

section

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleConstantDiagramColimit (cocone coneIsLimit isColimitCocone)
open PhilipponEtaleConstantDiagramSystem (ofSheafDiagram)

namespace PhilipponEtaleFilteredAcyclicity

universe u

/-- A filtered colimit of injective abelian étale sheaves has vanishing
positive cohomology on an affine scheme. -/
theorem acyclic_of_colimit {J : Type u} [Category.{u} J] [IsFiltered J]
    (X : Scheme.{u}) [IsAffine X] (F : J ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    [∀ i, Injective (F.obj i)] (d : Cocone F) (hd : IsColimit d) (q : ℕ) :
    Subsingleton (d.pt.H (q + 1)) := by
  let E := (opOpEquivalence J).functor
  let G := E ⋙ F
  let c := constCone Jᵒᵖ X
  let hc := coneIsLimit (I := Jᵒᵖ) X
  let S := ofSheafDiagram X G
  let : ∀ i, IsAffine (((Functor.const Jᵒᵖ).obj X).obj i) := fun _ => inferInstanceAs (IsAffine X)
  let : ∀ i, Injective (S.obj i) := fun i => inferInstanceAs (Injective (F.obj (E.obj (op i))))
  have h : Subsingleton ((cocone X G).pt.H (q + 1)) :=
    PhilipponEtaleLimitAcyclicity.acyclic c hc S q
  let hd' := (Functor.Final.isColimitWhiskerEquiv E d).symm hd
  let e := (isColimitCocone X G).coconePointUniqueUpToIso hd'
  let isom := ((Sheaf.functorH X.smallEtaleTopology (q + 1)).mapIso e).symm.addCommGroupIsoToAddEquiv
  exact ⟨fun x y => isom.injective (h.elim (isom x) (isom y))⟩

end PhilipponEtaleFilteredAcyclicity

end

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    {J : Type u} [Category.{u} J] [IsFiltered J]
    (X : Scheme.{u}) [IsAffine X] (F : J ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    [∀ i, Injective (F.obj i)] (d : Cocone F) (hd : IsColimit d) (q : ℕ) :
    Subsingleton (d.pt.H (q + 1)) := by
  exact
    PhilipponEtaleFilteredAcyclicity.acyclic_of_colimit X F d hd q

end

end
