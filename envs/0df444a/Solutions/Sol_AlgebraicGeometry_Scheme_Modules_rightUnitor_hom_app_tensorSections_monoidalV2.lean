-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.rightUnitor_hom_app_tensorSections_monoidalV2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/533dc87d-ff54-5a27-b4ec-954eb3618800

import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_rightUnitor_hom_app_tensorSections_monoidalV2

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_rightUnitor_hom_app_tensorSections_monoidalV2.AlgebraicGeometry"

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme Scheme.Modules Scheme.Modules.tensorSections"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "ringCatSheaf Γ Modules Opens PresheafOfModules Modules.sheafify Modules.tensorSections"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "tensor sheafify tensorSections"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace UnitorSections

open Opposite TensorProduct

variable {X : Scheme.{u}}

abbrev adj (X : Scheme.{u}) := SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property

abbrev ι (X : Scheme.{u}) := SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property

lemma sheafify_map_val_app_unit {P P' : X.PresheafOfModules} (g : P ⟶ P') (V : (X.Opens)ᵒᵖ) (z : P.obj V) :
    (((Modules.sheafify X).map g).val.app V) (((adj X).unit.app P).app V z) =
      ((adj X).unit.app P').app V (g.app V z) := by
  have h := (adj X).unit.naturality g
  exact (congr($(h.symm).app V z) :)

lemma counit_val_app_unit (N : X.Modules) (V : (X.Opens)ᵒᵖ) (y : N.val.obj V) :
    (((adj X).counit.app N).val.app V) (((adj X).unit.app ((ι X).obj N)).app V y) = y := by
  have h := (adj X).right_triangle_components N
  exact (congr($(h).app V y) :)

variable (N : X.Modules)

def tensorUnitIso : (Modules.sheafify X).obj ((ι X).obj N ⊗ 𝟙_ X.PresheafOfModules) ≅ N ⊗ 𝟙_ X.Modules :=
  (Functor.Monoidal.μIso (Modules.sheafify X) ((ι X).obj N) (𝟙_ X.PresheafOfModules)).symm ≪≫
    ((asIso (adj X).counit).app N ⊗ᵢ (Functor.Monoidal.εIso (Modules.sheafify X)).symm)

lemma tensorUnitIso_hom_comp_rightUnitor_hom :
    (tensorUnitIso N).hom ≫ (ρ_ N).hom =
      (Modules.sheafify X).map (ρ_ ((ι X).obj N)).hom ≫ (adj X).counit.app N := by
  dsimp only [tensorUnitIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, asIso_hom,
    MonoidalCategory.tensorIso_hom, Iso.symm_inv]
  rw [MonoidalCategory.tensorIso_hom, Iso.app_hom, asIso_hom, Iso.symm_hom]
  rw [Functor.Monoidal.μIso_inv, Functor.Monoidal.εIso_inv, Functor.Monoidal.map_rightUnitor,
    MonoidalCategory.tensorHom_def']
  simp only [Category.assoc]
  erw [← MonoidalCategory.rightUnitor_naturality ((adj X).counit.app N)]
  all_goals rfl

theorem rightUnitor_hom_app_tensorSections {U : X.Opens} (n : Γ(N, U)) (g : Γ(X, U)) :
    (ρ_ N).hom.app U (Modules.tensorSections (L := N) (M := 𝟙_ X.Modules) n g) = g • n := by
  have h := congr($(tensorUnitIso_hom_comp_rightUnitor_hom N).val.app (op U)
    (((adj X).unit.app ((ι X).obj N ⊗ 𝟙_ X.PresheafOfModules)).app (op U)
      ((n : N.val.obj (op U)) ⊗ₜ[Γ(X, U)] (g : (𝟙_ X.PresheafOfModules).obj (op U)))))
  have h' : (ρ_ N).hom.val.app (op U) ((tensorUnitIso N).hom.val.app (op U)
      (((adj X).unit.app ((ι X).obj N ⊗ 𝟙_ X.PresheafOfModules)).app (op U)
        ((n : N.val.obj (op U)) ⊗ₜ[Γ(X, U)] (g : (𝟙_ X.PresheafOfModules).obj (op U))))) =
      ((adj X).counit.app N).val.app (op U) (((Modules.sheafify X).map (ρ_ ((ι X).obj N)).hom).val.app (op U)
        (((adj X).unit.app ((ι X).obj N ⊗ 𝟙_ X.PresheafOfModules)).app (op U)
          ((n : N.val.obj (op U)) ⊗ₜ[Γ(X, U)] (g : (𝟙_ X.PresheafOfModules).obj (op U))))) := h
  change (ρ_ N).hom.val.app (op U) ((tensorUnitIso N).hom.val.app (op U)
      (((adj X).unit.app ((ι X).obj N ⊗ 𝟙_ X.PresheafOfModules)).app (op U)
        ((n : N.val.obj (op U)) ⊗ₜ[Γ(X, U)] (g : (𝟙_ X.PresheafOfModules).obj (op U))))) = g • n
  rw [h']
  letI : CommRing ((X.ringCatSheaf.obj).obj (op U)) := inferInstanceAs (CommRing Γ(X, U))

  exact (congrArg (((adj X).counit.app N).val.app (op U))
      (sheafify_map_val_app_unit (ρ_ ((ι X).obj N)).hom (op U) _)).trans
    ((counit_val_app_unit N (op U) _).trans (ModuleCat.MonoidalCategory.rightUnitor_hom_apply _ _))

end UnitorSections

end AlgebraicGeometry.Scheme.Modules

end

open CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_rightUnitor_hom_app_tensorSections_monoidalV2.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_rightUnitor_hom_app_tensorSections_monoidalV2.AlgebraicGeometry.Scheme.Modules in

theorem solution
    {X : Scheme.{u}} {N : X.Modules} {U : X.Opens} (n : Γ(N, U)) (g : Γ(X, U)) :
    (ρ_ N).hom.app U (AlgebraicGeometry.Scheme.Modules.tensorSections (L := N) (M := 𝟙_ X.Modules) n g) = g • n :=
  UnitorSections.rightUnitor_hom_app_tensorSections N n g

end S_AlgebraicGeometry_Scheme_Modules_rightUnitor_hom_app_tensorSections_monoidalV2
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_rightUnitor_hom_app_tensorSections_monoidalV2 (solution)
