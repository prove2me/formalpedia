-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.sheafify_mu_app_tensorSections_monoidalV2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/cc389315-baab-5539-a0fa-81c9b1a727df

import Mathlib
import Definitions.Def_PresheafOfModules_InternalHom
import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_sheafify_mu_app_tensorSections_monoidalV2

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_sheafify_mu_app_tensorSections_monoidalV2.AlgebraicGeometry"

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme Scheme.Modules Scheme.Modules.sheafify Scheme.Modules.tensorSections"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "ringCatSheaf Γ Modules Opens PresheafOfModules Modules.sheafify Modules.tensorSections"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "tensor sheafify tensorIsoSheafify tensorSections"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace SheafifyMu

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Opposite TensorProduct"

variable {X : Scheme.{u}}

abbrev adj (X : Scheme.{u}) := SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property

abbrev ι (X : Scheme.{u}) := SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property

variable (L M : X.Modules)

def sheafifyTensorIso : (Modules.sheafify X).obj ((ι X).obj L ⊗ (ι X).obj M) ≅ L ⊗ M :=
  (Functor.Monoidal.μIso (Modules.sheafify X) ((ι X).obj L) ((ι X).obj M)).symm ≪≫
    ((asIso (adj X).counit).app L ⊗ᵢ (asIso (adj X).counit).app M)

variable {L M}

lemma tensorSections_eq {U : X.Opens} (s : Γ(L, U)) (t : Γ(M, U)) :
    Modules.tensorSections s t = (sheafifyTensorIso L M).hom.val.app (op U)
      (((adj X).unit.app ((ι X).obj L ⊗ (ι X).obj M)).app (op U)
        ((s : L.val.obj (op U)) ⊗ₜ[Γ(X, U)] (t : M.val.obj (op U)))) := rfl

lemma sheafify_map_val_app_unit {P P' : X.PresheafOfModules} (g : P ⟶ P') (V : (X.Opens)ᵒᵖ) (z : P.obj V) :
    (((Modules.sheafify X).map g).val.app V) (((adj X).unit.app P).app V z) =
      ((adj X).unit.app P').app V (g.app V z) := by
  have h := (adj X).unit.naturality g
  exact (congr($(h.symm).app V z) :)

lemma map_tensorHom_unit_comp (P Q : X.PresheafOfModules) :
    (Modules.sheafify X).map ((adj X).unit.app P ⊗ₘ (adj X).unit.app Q) ≫
      (sheafifyTensorIso ((Modules.sheafify X).obj P) ((Modules.sheafify X).obj Q)).hom ≫
        Functor.LaxMonoidal.μ (Modules.sheafify X) P Q = 𝟙 _ := by
  have hP : (Modules.sheafify X).map ((adj X).unit.app P) ≫ (adj X).counit.app ((Modules.sheafify X).obj P) =
      𝟙 _ := (adj X).left_triangle_components P
  have hQ : (Modules.sheafify X).map ((adj X).unit.app Q) ≫ (adj X).counit.app ((Modules.sheafify X).obj Q) =
      𝟙 _ := (adj X).left_triangle_components Q
  dsimp only [sheafifyTensorIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, asIso_hom,
    MonoidalCategory.tensorIso_hom]
  rw [Functor.Monoidal.μIso_inv]
  simp only [← Category.assoc]
  erw [← Functor.OplaxMonoidal.δ_natural (Modules.sheafify X) ((adj X).unit.app P) ((adj X).unit.app Q)]
  rw [Category.assoc (Functor.OplaxMonoidal.δ (Modules.sheafify X) _ _)]
  erw [MonoidalCategory.tensorHom_comp_tensorHom, hP, hQ]
  erw [MonoidalCategory.id_tensorHom_id, Category.comp_id]
  exact Functor.Monoidal.δ_μ _ _ _

theorem sheafify_μ_app_tensorSections (P Q : X.PresheafOfModules) {U : X.Opens}
    (x : P.obj (op U)) (y : Q.obj (op U)) :
    (Functor.LaxMonoidal.μ (Modules.sheafify X) P Q).app U
      (Modules.tensorSections (L := (Modules.sheafify X).obj P) (M := (Modules.sheafify X).obj Q)
        (((adj X).unit.app P).app (op U) x) (((adj X).unit.app Q).app (op U) y)) =
    ((adj X).unit.app (P ⊗ Q)).app (op U) (x ⊗ₜ[Γ(X, U)] y) := by

  have H := congr($(map_tensorHom_unit_comp P Q).val.app (op U)
    (((adj X).unit.app (P ⊗ Q)).app (op U) (x ⊗ₜ[Γ(X, U)] y)))

  have h1 := (sheafify_map_val_app_unit ((adj X).unit.app P ⊗ₘ (adj X).unit.app Q) (op U)
      (x ⊗ₜ[Γ(X, U)] y)).trans
    (congrArg (((adj X).unit.app ((ι X).obj ((Modules.sheafify X).obj P) ⊗
        (ι X).obj ((Modules.sheafify X).obj Q))).app (op U))
      (ModuleCat.MonoidalCategory.tensorHom_tmul (((adj X).unit.app P).app (op U))
        (((adj X).unit.app Q).app (op U)) x y))
  exact (congrArg (fun z => (Functor.LaxMonoidal.μ (Modules.sheafify X) P Q).val.app (op U)
    ((sheafifyTensorIso ((Modules.sheafify X).obj P) ((Modules.sheafify X).obj Q)).hom.val.app (op U) z))
      h1).symm.trans H

end SheafifyMu

end AlgebraicGeometry.Scheme.Modules

end

open CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_sheafify_mu_app_tensorSections_monoidalV2.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_sheafify_mu_app_tensorSections_monoidalV2.AlgebraicGeometry.Scheme.Modules TensorProduct in

theorem solution {X : AlgebraicGeometry.Scheme.{u}} (P Q : X.PresheafOfModules) {U : X.Opens}
    (x : P.obj (Opposite.op U)) (y : Q.obj (Opposite.op U)) :
    (Functor.LaxMonoidal.μ (AlgebraicGeometry.Scheme.Modules.sheafify X) P Q).app U
      (AlgebraicGeometry.Scheme.Modules.tensorSections
        (L := (AlgebraicGeometry.Scheme.Modules.sheafify X).obj P)
        (M := (AlgebraicGeometry.Scheme.Modules.sheafify X).obj Q)
        (((SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property).unit.app P).app (Opposite.op U) x)
        (((SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property).unit.app Q).app (Opposite.op U) y)) =
    ((SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property).unit.app (P ⊗ Q)).app (Opposite.op U)
      (x ⊗ₜ[Γ(X, U)] y) :=
  SheafifyMu.sheafify_μ_app_tensorSections P Q x y

end S_AlgebraicGeometry_Scheme_Modules_sheafify_mu_app_tensorSections_monoidalV2
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_sheafify_mu_app_tensorSections_monoidalV2 (solution)
