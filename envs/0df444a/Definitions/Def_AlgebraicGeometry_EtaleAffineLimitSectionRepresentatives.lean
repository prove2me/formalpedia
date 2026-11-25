-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleAffineLimitSectionRepresentatives
-- name    : AlgebraicGeometry_EtaleAffineLimitSectionRepresentatives
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-25T08:00:09.53787+00:00
-- url     : https://prove2.me/theorems/61fe2f3f-02ae-5a85-ae03-70038d8bdd5e
-- title:
--   Lifting global étale sections to an affine stage
-- statement:
--   The presentation of global sections as a filtered colimit lets every global section come from a compatible coefficient sheaf at a stage.
-- source:
--   Stacks Project, Lemmas 59.51.4, 59.73.2 and 59.74.4, https://stacks.math.columbia.edu/tag/03Q5.

import Definitions.Def_AlgebraicGeometry_EtaleAffineLimitGlobalSections
import Mathlib.Algebra.Category.Grp.FilteredColimits

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponCompatibleInjectiveSystems (System)
open PhilipponEtaleAcyclicCohomology (globalSections)
open PhilipponEtaleDirectImageSystem (directImages)
open PhilipponEtaleLimitGlobalSections (sectionsDiagram evalIso colimIso)
open PhilipponEtaleLimitSectionProjections (stageSections ι_colimIso)
open PhilipponEtaleLimitSheaf (limitSheaf)

namespace PhilipponEtaleLimitSectionSurjectivity

universe u

/-- Each global section on the limit has a representative at a stage. -/
theorem exists_stage_section {I : Type u} [Category.{u} I] [IsCofiltered I]
    {D : I ⥤ Scheme.{u}} [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c)
    (i : I) (F : System (directImages D))
    (s : (globalSections c.pt).obj (limitSheaf c hc F)) :
    ∃ (j : I) (t : (globalSections (D.obj j)).obj (F.obj j)), stageSections c hc F j t = s := by
  let P := (sectionsDiagram c hc i).obj F
  let e := (colimIso c hc i).app F
  let U := forget AddCommGrpCat.{u}
  obtain ⟨j, z, hz⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves U (colimit.isColimit P)) (e.inv s)
  refine ⟨j.unop.left, ((evalIso c hc i j).app F).hom z, ?_⟩
  calc
    _ = e.hom (colimit.ι P j z) :=
      (ConcreteCategory.congr_hom (ι_colimIso c hc i F j) z).symm
    _ = e.hom (e.inv s) := congrArg (fun y => e.hom y) hz
    _ = s := ConcreteCategory.congr_hom e.inv_hom_id s

end PhilipponEtaleLimitSectionSurjectivity

end

end


