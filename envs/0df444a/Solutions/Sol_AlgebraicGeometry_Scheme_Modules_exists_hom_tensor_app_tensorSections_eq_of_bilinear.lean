-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_hom_tensor_app_tensorSections_eq_of_bilinear
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/ad0862b8-42b7-5976-b1a4-218c553940b7

import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_hom_tensor_app_tensorSections_eq_of_bilinear

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_hom_tensor_app_tensorSections_eq_of_bilinear.AlgebraicGeometry Opposite TensorProduct"
p2m_open "CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Scheme Scheme.Modules.Hom.app Scheme.Modules Scheme.Modules.tensorSections"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "ringCatSheaf Hom Γ Modules.Hom.comp_app Hom.app Modules.Hom Modules.Hom.app Hom.comp_app Modules Opens PresheafOfModules evaluation Modules.sheafify Modules.tensorSections"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "presheaf Hom.comp_app Hom Hom.app tensor sheafify tensorIsoSheafify tensorSections"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace TensorDescV2

abbrev adj (Z : Scheme.{u}) := SheafOfModules.sheafifyAdj Z.sheaf.obj Z.ringCatSheaf.property

abbrev ι (Z : Scheme.{u}) := SheafOfModules.toPMod Z.sheaf.obj Z.ringCatSheaf.property

def shUnit {Z : Scheme.{u}} (A : Z.PresheafOfModules) (W : Z.Opens) (a : A.obj (op W)) :
    Γ((Modules.sheafify Z).obj A, W) :=
  ((adj Z).unit.app A).app (op W) a

lemma sheafify_map_app_shUnit {Z : Scheme.{u}} {A A' : Z.PresheafOfModules} (g : A ⟶ A') (W : Z.Opens)
    (z : A.obj (op W)) :
    Scheme.Modules.Hom.app ((Modules.sheafify Z).map g) W (shUnit A W z) = shUnit A' W (g.app (op W) z) := by
  have h := (adj Z).unit.naturality g
  exact (congr($(h.symm).app (op W) z) :)

variable {Y : Scheme.{u}}

lemma counit_app_shUnit (P : Y.Modules) (W : Y.Opens) (y : ((ι Y).obj P).obj (op W)) :
    Scheme.Modules.Hom.app ((adj Y).counit.app P) W (shUnit ((ι Y).obj P) W y) = y := by
  have h := (adj Y).right_triangle_components P
  exact (congr($(h).app (op W) y) :)

def cmpIso (L M : Y.Modules) : (Modules.sheafify Y).obj ((ι Y).obj L ⊗ (ι Y).obj M) ≅ L ⊗ M :=
  (Functor.Monoidal.μIso (Modules.sheafify Y) ((ι Y).obj L) ((ι Y).obj M)).symm ≪≫
    ((asIso (adj Y).counit).app L ⊗ᵢ (asIso (adj Y).counit).app M)

lemma tensorSections_eq (L M : Y.Modules) (V : Y.Opens) (s : Γ(L, V)) (t : Γ(M, V)) :
    Modules.tensorSections s t = Scheme.Modules.Hom.app (cmpIso L M).hom V
      (shUnit ((ι Y).obj L ⊗ (ι Y).obj M) V ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y, V)] (t : M.val.obj (op V)))) := rfl

section Beta

variable (L M P : Y.Modules)
  (B : ∀ U : Y.Opens, Γ(L, U) →ₗ[Γ(Y, U)] Γ(M, U) →ₗ[Γ(Y, U)] Γ(P, U))

def Bι (V : (Y.Opens)ᵒᵖ) :
    ((ι Y).obj L).obj V →ₗ[((Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj V)]
      ((ι Y).obj M).obj V →ₗ[((Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj V)] ((ι Y).obj P).obj V :=
  B V.unop

def βapp (V : (Y.Opens)ᵒᵖ) : ((ι Y).obj L ⊗ (ι Y).obj M).obj V ⟶ ((ι Y).obj P).obj V :=
  ModuleCat.ofHom (TensorProduct.lift (Bι L M P B V))

lemma βapp_tmul (V : (Y.Opens)ᵒᵖ) (s : ((ι Y).obj L).obj V) (t : ((ι Y).obj M).obj V) :
    (βapp L M P B V).hom (s ⊗ₜ t) = Bι L M P B V s t :=
  TensorProduct.lift.tmul s t

omit B in

lemma ιtensor_map_tmul {V W : (Y.Opens)ᵒᵖ} (i : V ⟶ W) (s : ((ι Y).obj L).obj V) (t : ((ι Y).obj M).obj V) :
    DFunLike.coe (α := (((ι Y).obj L).obj V ⊗ ((ι Y).obj M).obj V :))
      (β := fun _ => (ModuleCat.restrictScalars ((Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat).map i).hom).obj
        (((ι Y).obj L).obj W ⊗ ((ι Y).obj M).obj W))
      (ModuleCat.Hom.hom (((ι Y).obj L ⊗ (ι Y).obj M).map i)) (s ⊗ₜ t)
      = ((ι Y).obj L).map i s ⊗ₜ ((ι Y).obj M).map i t :=
  PresheafOfModules.Monoidal.tensorObj_map_tmul i s t

variable (hB : ∀ {U V : Y.Opens} (i : V ⟶ U) (s : Γ(L, U)) (t : Γ(M, U)),
      P.presheaf.map i.op (B U s t) = B V (L.presheaf.map i.op s) (M.presheaf.map i.op t))

include hB in
set_option maxHeartbeats 6400000 in

def β : (ι Y).obj L ⊗ (ι Y).obj M ⟶ (ι Y).obj P where
  app V := βapp L M P B V
  naturality {V W} i := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro s t
    exact (hB i.unop s t).symm

lemma β_app_tmul (V : Y.Opens) (s : Γ(L, V)) (t : Γ(M, V)) :
    (β L M P B hB).app (op V) ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y, V)] (t : M.val.obj (op V))) = B V s t :=
  βapp_tmul L M P B (op V) s t

def ν : L ⊗ M ⟶ P :=
  (cmpIso L M).inv ≫ ((adj Y).homEquiv _ _).symm (β L M P B hB)

lemma cmpIso_hom_ν : (cmpIso L M).hom ≫ ν L M P B hB = ((adj Y).homEquiv _ _).symm (β L M P B hB) := by
  rw [ν, Iso.hom_inv_id_assoc]

lemma ν_app_tensorSections (V : Y.Opens) (s : Γ(L, V)) (t : Γ(M, V)) :
    Scheme.Modules.Hom.app (ν L M P B hB) V (Modules.tensorSections s t) = B V s t := by
  rw [tensorSections_eq]
  change Scheme.Modules.Hom.app ((cmpIso L M).hom ≫ ν L M P B hB) V
      (shUnit ((ι Y).obj L ⊗ (ι Y).obj M) V ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y, V)] (t : M.val.obj (op V)))) = B V s t
  rw [cmpIso_hom_ν, Adjunction.homEquiv_counit, Scheme.Modules.Hom.comp_app]
  change Scheme.Modules.Hom.app ((adj Y).counit.app P) V
      (Scheme.Modules.Hom.app ((Modules.sheafify Y).map (β L M P B hB)) V
        (shUnit ((ι Y).obj L ⊗ (ι Y).obj M) V ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y, V)] (t : M.val.obj (op V))))) = B V s t
  rw [sheafify_map_app_shUnit]
  exact (congrArg (fun y => Scheme.Modules.Hom.app ((adj Y).counit.app P) V (shUnit ((ι Y).obj P) V y))
    (β_app_tmul L M P B hB V s t)).trans (counit_app_shUnit P V _)

end Beta

end TensorDescV2

end AlgebraicGeometry.Scheme.Modules

end

open _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_hom_tensor_app_tensorSections_eq_of_bilinear.AlgebraicGeometry.Scheme.Modules in
theorem solution
    {X : Scheme.{u}} (L M P : X.Modules)
    (B : ∀ U : X.Opens, Γ(L, U) →ₗ[Γ(X, U)] Γ(M, U) →ₗ[Γ(X, U)] Γ(P, U))
    (hB : ∀ {U V : X.Opens} (i : V ⟶ U) (s : Γ(L, U)) (t : Γ(M, U)),
      P.presheaf.map i.op (B U s t) = B V (L.presheaf.map i.op s) (M.presheaf.map i.op t)) :
    ∃ ν : L ⊗ M ⟶ P, ∀ (U : X.Opens) (s : Γ(L, U)) (t : Γ(M, U)),
      ν.app U (Scheme.Modules.tensorSections s t) = B U s t :=
  ⟨TensorDescV2.ν L M P B hB, fun U s t => TensorDescV2.ν_app_tensorSections L M P B hB U s t⟩

end S_AlgebraicGeometry_Scheme_Modules_exists_hom_tensor_app_tensorSections_eq_of_bilinear
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_hom_tensor_app_tensorSections_eq_of_bilinear (solution)
