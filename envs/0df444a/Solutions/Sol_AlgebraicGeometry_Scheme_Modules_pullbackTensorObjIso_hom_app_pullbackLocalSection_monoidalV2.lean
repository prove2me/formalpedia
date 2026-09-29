-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso_hom_app_pullbackLocalSection_monoidalV2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/dcaab3bf-d5ca-5a00-b337-62fc78bc063d

import Mathlib
import Definitions.Def_PresheafOfModules_InternalHom
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_PresheafOfModules_PullbackMonoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackTensorObjIso_hom_app_pullbackLocalSection_monoidalV2

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackTensorObjIso_hom_app_pullbackLocalSection_monoidalV2.AlgebraicGeometry Opposite TensorProduct"
p2m_open "CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Scheme Scheme.Modules.Hom.app Scheme.Modules Scheme.Modules.pullbackTensorObjIso Scheme.Modules.tensorSections Scheme.Modules.pullbackLocalSection"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "ringCatSheaf Modules.pullback Hom Γ Modules.Hom.comp_app Hom.app Modules.Hom Modules.Hom.app Hom.comp_app Modules Opens grothendieckTopology PresheafOfModules Modules.sheafify Modules.pullbackTensorObjIso Modules.tensorSections Modules.pullbackLocalSection"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "pullback presheaf Hom.comp_app Hom Hom.app pullbackPushforwardAdjunction tensor sheafify tensorIsoSheafify pullback₀ pullbackTensorObjIso tensorSections pullbackLocalSection pullbackLocalSection_app"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace PullbackTensorSections

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

private abbrev _root_.AlgebraicGeometry.Scheme.Modules.PullbackTensorSections.adj (Z : Scheme.{u}) := SheafOfModules.sheafifyAdj Z.sheaf.obj Z.ringCatSheaf.property
p2m_export "AlgebraicGeometry.Scheme.Modules.PullbackTensorSections" "adj"

abbrev ι (Z : Scheme.{u}) := SheafOfModules.toPMod Z.sheaf.obj Z.ringCatSheaf.property

private abbrev _root_.AlgebraicGeometry.Scheme.Modules.PullbackTensorSections.pf := PresheafOfModules.PullbackMonoidal.pf (TopologicalSpace.Opens.map f.base)
  (R := X.sheaf.obj) (S := Y.sheaf.obj) f.c
p2m_export "AlgebraicGeometry.Scheme.Modules.PullbackTensorSections" "pf"

abbrev adj₀ := PresheafOfModules.PullbackMonoidal.adj (TopologicalSpace.Opens.map f.base)
  (R := X.sheaf.obj) (S := Y.sheaf.obj) f.c

abbrev e : Modules.sheafify Y ⋙ Modules.pullback f ≅ pullback₀ f ⋙ Modules.sheafify X :=
  SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom

def pb₀Section (P : Y.PresheafOfModules) (V : Y.Opens) (s : P.obj (op V)) :
    ((pullback₀ f).obj P).obj (op (f ⁻¹ᵁ V)) :=
  ((adj₀ f).unit.app P).app (op V) s

def shUnit {Z : Scheme.{u}} (A : Z.PresheafOfModules) (W : Z.Opens) (a : A.obj (op W)) :
    Γ((Modules.sheafify Z).obj A, W) :=
  ((adj Z).unit.app A).app (op W) a

example : pullback₀ f = PresheafOfModules.pullback f.toRingCatSheafHom.hom := rfl
example : adj₀ f = PresheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom.hom := rfl
example : e f =
    Localization.Lifting.iso (Modules.sheafify Y)
      (SheafOfModules.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj)
      (pullback₀ f ⋙ Modules.sheafify X) (Modules.pullback f) := rfl

lemma sheafify_map_app_shUnit {Z : Scheme.{u}} {A A' : Z.PresheafOfModules} (g : A ⟶ A') (W : Z.Opens)
    (z : A.obj (op W)) :
    Scheme.Modules.Hom.app ((Modules.sheafify Z).map g) W (shUnit A W z) = shUnit A' W (g.app (op W) z) := by
  have h := (adj Z).unit.naturality g
  exact (congr($(h.symm).app (op W) z) :)

lemma counit_app_shUnit (L : Y.Modules) (V : Y.Opens) (s : Γ(L, V)) :
    Scheme.Modules.Hom.app ((adj Y).counit.app L) V (shUnit ((ι Y).obj L) V s) = s := by
  have h := (adj Y).right_triangle_components L
  exact (congr($(h).app (op V) s) :)

lemma homEquiv_symm_app_pb₀Section {A : Y.PresheafOfModules} {B : X.PresheafOfModules}
    (k : A ⟶ (pf f).obj B) (V : Y.Opens) (z : A.obj (op V)) :
    (((adj₀ f).homEquiv A B).symm k).app (op (f ⁻¹ᵁ V)) (pb₀Section f A V z) =
      (k.app (op V) z : B.obj (op (f ⁻¹ᵁ V))) := by
  have h1 := (adj₀ f).homEquiv_unit (X := A) (Y := B) (f := ((adj₀ f).homEquiv A B).symm k)
  rw [Equiv.apply_symm_apply] at h1
  exact (congr($(h1.symm).app (op V) z) :)

lemma e_hom_app_pullbackLocalSection (P : Y.PresheafOfModules) (V : Y.Opens) (s : P.obj (op V)) :
    Scheme.Modules.Hom.app ((e f).hom.app P) (f ⁻¹ᵁ V) (pullbackLocalSection f (shUnit P V s)) =
      shUnit ((pullback₀ f).obj P) (f ⁻¹ᵁ V) (pb₀Section f P V s) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).comp
      (SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom))
    ((PresheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom.hom).comp
      (PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj))) P
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app] at h
  exact (congr($(h).app (op V) s) :)

lemma e_inv_app_shUnit (P : Y.PresheafOfModules) (V : Y.Opens) (s : P.obj (op V)) :
    Scheme.Modules.Hom.app ((e f).inv.app P) (f ⁻¹ᵁ V) (shUnit ((pullback₀ f).obj P) (f ⁻¹ᵁ V) (pb₀Section f P V s)) =
      pullbackLocalSection f (shUnit P V s) := by
  rw [← e_hom_app_pullbackLocalSection]
  change Scheme.Modules.Hom.app ((e f).hom.app P ≫ (e f).inv.app P) (f ⁻¹ᵁ V) _ = _
  rw [Iso.hom_inv_id_app]
  rfl

lemma pb₀_δ_eq (P Q : Y.PresheafOfModules) :
    δ (pullback₀ f) P Q = ((adj₀ f).homEquiv _ _).symm
      (((adj₀ f).unit.app P ⊗ₘ (adj₀ f).unit.app Q) ≫ μ (pf f) _ _) := by
  exact Adjunction.leftAdjointOplaxMonoidal_δ (adj₀ f) P Q

lemma pb₀_δ_app_pb₀Section_tmul (P Q : Y.PresheafOfModules) (V : Y.Opens) (x : P.obj (op V)) (y : Q.obj (op V)) :
    (δ (pullback₀ f) P Q).app (op (f ⁻¹ᵁ V)) (pb₀Section f (P ⊗ Q) V (x ⊗ₜ[Γ(Y, V)] y)) =
      (pb₀Section f P V x ⊗ₜ[Γ(X, f ⁻¹ᵁ V)] pb₀Section f Q V y :
        (((pullback₀ f).obj P).obj (op (f ⁻¹ᵁ V)) ⊗ ((pullback₀ f).obj Q).obj (op (f ⁻¹ᵁ V)) :)) := by
  rw [pb₀_δ_eq]
  refine (homEquiv_symm_app_pb₀Section f
    (((adj₀ f).unit.app P ⊗ₘ (adj₀ f).unit.app Q) ≫ μ (pf f) _ _) V (x ⊗ₜ[Γ(Y, V)] y)).trans ?_
  change (μ (pf f) ((pullback₀ f).obj P) ((pullback₀ f).obj Q)).app (op V)
    ((((adj₀ f).unit.app P ⊗ₘ (adj₀ f).unit.app Q)).app (op V) (x ⊗ₜ[Γ(Y, V)] y)) = _
  erw [PresheafOfModules.PullbackMonoidal.tensorHom_app_tmul]
  erw [PresheafOfModules.PullbackMonoidal.pf_μ_app_tmul]
  rfl

def cmpIso (L M : Y.Modules) : (Modules.sheafify Y).obj ((ι Y).obj L ⊗ (ι Y).obj M) ≅ L ⊗ M :=
  (Functor.Monoidal.μIso (Modules.sheafify Y) ((ι Y).obj L) ((ι Y).obj M)).symm ≪≫
    ((asIso (adj Y).counit).app L ⊗ᵢ (asIso (adj Y).counit).app M)

lemma cmpIso_hom (L M : Y.Modules) :
    (cmpIso L M).hom = δ (Modules.sheafify Y) ((ι Y).obj L) ((ι Y).obj M) ≫
      ((adj Y).counit.app L ⊗ₘ (adj Y).counit.app M) := rfl

lemma tensorSections_eq (L M : Y.Modules) (V : Y.Opens) (s : Γ(L, V)) (t : Γ(M, V)) :
    Modules.tensorSections s t = Scheme.Modules.Hom.app (cmpIso L M).hom V
      (shUnit ((ι Y).obj L ⊗ (ι Y).obj M) V ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y, V)] (t : M.val.obj (op V)))) := rfl

lemma cmpIso_hom_comp_tensorHom {L L' M M' : Y.Modules} (φ : L ⟶ L') (ψ : M ⟶ M') :
    (cmpIso L M).hom ≫ (φ ⊗ₘ ψ) =
      (Modules.sheafify Y).map ((ι Y).map φ ⊗ₘ (ι Y).map ψ) ≫ (cmpIso L' M').hom := by
  have hφ := (adj Y).counit.naturality φ
  have hψ := (adj Y).counit.naturality ψ
  simp only [Functor.comp_map, Functor.id_map] at hφ hψ
  have hε : ((adj Y).counit.app L ⊗ₘ (adj Y).counit.app M) ≫ (φ ⊗ₘ ψ) =
      ((Modules.sheafify Y).map ((ι Y).map φ) ⊗ₘ (Modules.sheafify Y).map ((ι Y).map ψ)) ≫
        ((adj Y).counit.app L' ⊗ₘ (adj Y).counit.app M') := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom]
    erw [← hφ, ← hψ]
    rfl
  have hδ := Functor.OplaxMonoidal.δ_natural (Modules.sheafify Y) ((ι Y).map φ) ((ι Y).map ψ)
  rw [cmpIso_hom, cmpIso_hom, Category.assoc, hε, ← Category.assoc]
  erw [hδ]
  rw [Category.assoc]

lemma tensorHom_app_tensorSections_inl {L L' M M' : Y.Modules} (φ : L ⟶ L') (ψ : M ⟶ M') (V : Y.Opens)
    (s : Γ(L, V)) (t : Γ(M, V)) :
    Scheme.Modules.Hom.app (φ ⊗ₘ ψ) V (Modules.tensorSections s t) =
      Modules.tensorSections (Scheme.Modules.Hom.app φ V s) (Scheme.Modules.Hom.app ψ V t) := by
  have h := congr(Scheme.Modules.Hom.app $(cmpIso_hom_comp_tensorHom φ ψ) V
    (shUnit ((ι Y).obj L ⊗ (ι Y).obj M) V ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y, V)] (t : M.val.obj (op V)))))
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app] at h
  change Scheme.Modules.Hom.app (φ ⊗ₘ ψ) V (Scheme.Modules.Hom.app (cmpIso L M).hom V
      (shUnit ((ι Y).obj L ⊗ (ι Y).obj M) V ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y, V)] (t : M.val.obj (op V))))) =
    Scheme.Modules.Hom.app (cmpIso L' M').hom V (Scheme.Modules.Hom.app
      ((Modules.sheafify Y).map ((ι Y).map φ ⊗ₘ (ι Y).map ψ)) V
      (shUnit ((ι Y).obj L ⊗ (ι Y).obj M) V ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y, V)] (t : M.val.obj (op V))))) at h
  rw [sheafify_map_app_shUnit] at h
  erw [PresheafOfModules.PullbackMonoidal.tensorHom_app_tmul] at h
  rw [tensorSections_eq, tensorSections_eq]
  exact h

lemma sheafify_map_unit_tensor_unit_comp_cmpIso_hom (A B : X.PresheafOfModules) :
    (Modules.sheafify X).map ((adj X).unit.app A ⊗ₘ (adj X).unit.app B) ≫
        (cmpIso ((Modules.sheafify X).obj A) ((Modules.sheafify X).obj B)).hom =
      δ (Modules.sheafify X) A B := by
  have hδ := Functor.OplaxMonoidal.δ_natural (Modules.sheafify X) ((adj X).unit.app A) ((adj X).unit.app B)
  have hA := (adj X).left_triangle_components A
  have hB := (adj X).left_triangle_components B
  rw [cmpIso_hom, ← Category.assoc]
  erw [← hδ]
  rw [Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]
  erw [hA, hB, MonoidalCategory.id_tensorHom_id, Category.comp_id]
  rfl

lemma sheafify_δ_app_shUnit_tmul (A B : X.PresheafOfModules) (W : X.Opens) (a : A.obj (op W)) (b : B.obj (op W)) :
    (δ (Modules.sheafify X) A B).app W (shUnit (A ⊗ B) W (a ⊗ₜ[Γ(X, W)] b)) =
      Modules.tensorSections (L := (Modules.sheafify X).obj A) (M := (Modules.sheafify X).obj B)
        (shUnit A W a) (shUnit B W b) := by
  have h := congr(Scheme.Modules.Hom.app $(sheafify_map_unit_tensor_unit_comp_cmpIso_hom A B) W
    (shUnit (A ⊗ B) W (a ⊗ₜ[Γ(X, W)] b)))
  rw [Scheme.Modules.Hom.comp_app] at h
  change Scheme.Modules.Hom.app (cmpIso ((Modules.sheafify X).obj A) ((Modules.sheafify X).obj B)).hom W
      (Scheme.Modules.Hom.app ((Modules.sheafify X).map ((adj X).unit.app A ⊗ₘ (adj X).unit.app B)) W
        (shUnit (A ⊗ B) W (a ⊗ₜ[Γ(X, W)] b))) = _ at h
  erw [sheafify_map_app_shUnit] at h
  erw [PresheafOfModules.PullbackMonoidal.tensorHom_app_tmul] at h
  rw [tensorSections_eq]
  exact h.symm

lemma e_hom_app_tensor_comp_δ (P Q : Y.PresheafOfModules) :
    (e f).hom.app (P ⊗ Q) ≫ δ (pullback₀ f ⋙ Modules.sheafify X) P Q =
      δ (Modules.sheafify Y ⋙ Modules.pullback f) P Q ≫ ((e f).hom.app P ⊗ₘ (e f).hom.app Q) := by
  letI := SheafOfModules.presheafW_isMonoidal Y.sheaf.obj Y.ringCatSheaf.property
  haveI hmon : NatTrans.IsMonoidal (F₁ := Modules.sheafify Y ⋙ Modules.pullback f)
      (F₂ := pullback₀ f ⋙ Modules.sheafify X) (e f).hom :=
    Localization.Monoidal.lifting_isMonoidal (Modules.sheafify Y)
      (SheafOfModules.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj)
      (Modules.pullback f) (pullback₀ f ⋙ Modules.sheafify X)
  have T := hmon.tensor P Q
  calc (e f).hom.app (P ⊗ Q) ≫ δ (pullback₀ f ⋙ Modules.sheafify X) P Q
      = (δ (Modules.sheafify Y ⋙ Modules.pullback f) P Q ≫ μ (Modules.sheafify Y ⋙ Modules.pullback f) P Q) ≫
          (e f).hom.app (P ⊗ Q) ≫ δ (pullback₀ f ⋙ Modules.sheafify X) P Q := by
        rw [Functor.Monoidal.δ_μ, Category.id_comp]
    _ = δ (Modules.sheafify Y ⋙ Modules.pullback f) P Q ≫
          (((e f).hom.app P ⊗ₘ (e f).hom.app Q) ≫ μ (pullback₀ f ⋙ Modules.sheafify X) P Q) ≫
            δ (pullback₀ f ⋙ Modules.sheafify X) P Q := by
        rw [← T]; simp only [Category.assoc]
    _ = δ (Modules.sheafify Y ⋙ Modules.pullback f) P Q ≫ ((e f).hom.app P ⊗ₘ (e f).hom.app Q) := by
        rw [Category.assoc, Functor.Monoidal.μ_δ, Category.comp_id]

lemma δ_sheafify_comp_pullback_eq (P Q : Y.PresheafOfModules) :
    δ (Modules.sheafify Y ⋙ Modules.pullback f) P Q =
      (e f).hom.app (P ⊗ Q) ≫
        ((Modules.sheafify X).map (δ (pullback₀ f) P Q) ≫
          δ (Modules.sheafify X) ((pullback₀ f).obj P) ((pullback₀ f).obj Q)) ≫
        ((e f).inv.app P ⊗ₘ (e f).inv.app Q) := by
  rw [← Functor.OplaxMonoidal.comp_δ, ← Category.assoc, e_hom_app_tensor_comp_δ, Category.assoc,
    MonoidalCategory.tensorHom_comp_tensorHom, Iso.hom_inv_id_app, Iso.hom_inv_id_app,
    MonoidalCategory.id_tensorHom_id, Category.comp_id]

theorem pullbackTensorObjIso_hom_app_pullbackLocalSection_tensorSections (L M : Y.Modules) (V : Y.Opens)
    (s : Γ(L, V)) (t : Γ(M, V)) :
    ((pullbackTensorObjIso f L M).hom.app (f ⁻¹ᵁ V)) (pullbackLocalSection f (Modules.tensorSections s t)) =
      Modules.tensorSections (pullbackLocalSection f s) (pullbackLocalSection f t) := by
  have hnat := Functor.OplaxMonoidal.δ_natural (Modules.pullback f)
    ((adj Y).counit.app L) ((adj Y).counit.app M)

  have key :
    Scheme.Modules.Hom.app (δ (Modules.sheafify Y ⋙ Modules.pullback f) ((ι Y).obj L) ((ι Y).obj M)) (f ⁻¹ᵁ V)
      (pullbackLocalSection f (shUnit ((ι Y).obj L ⊗ (ι Y).obj M) V
        ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y, V)] (t : M.val.obj (op V))))) =
      Modules.tensorSections (pullbackLocalSection f (shUnit ((ι Y).obj L) V s))
        (pullbackLocalSection f (shUnit ((ι Y).obj M) V t)) := by
    rw [δ_sheafify_comp_pullback_eq]
    change Scheme.Modules.Hom.app ((e f).inv.app ((ι Y).obj L) ⊗ₘ (e f).inv.app ((ι Y).obj M)) (f ⁻¹ᵁ V)
      (Scheme.Modules.Hom.app (δ (Modules.sheafify X) ((pullback₀ f).obj ((ι Y).obj L))
          ((pullback₀ f).obj ((ι Y).obj M))) (f ⁻¹ᵁ V)
        (Scheme.Modules.Hom.app ((Modules.sheafify X).map (δ (pullback₀ f) ((ι Y).obj L) ((ι Y).obj M)))
            (f ⁻¹ᵁ V)
          (Scheme.Modules.Hom.app ((e f).hom.app ((ι Y).obj L ⊗ (ι Y).obj M)) (f ⁻¹ᵁ V)
            (pullbackLocalSection f (shUnit ((ι Y).obj L ⊗ (ι Y).obj M) V
              ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y, V)] (t : M.val.obj (op V)))))))) = _
    rw [e_hom_app_pullbackLocalSection, sheafify_map_app_shUnit]
    erw [pb₀_δ_app_pb₀Section_tmul]
    rw [sheafify_δ_app_shUnit_tmul]
    erw [tensorHom_app_tensorSections_inl]
    rw [e_inv_app_shUnit, e_inv_app_shUnit]

  calc ((pullbackTensorObjIso f L M).hom.app (f ⁻¹ᵁ V)) (pullbackLocalSection f (Modules.tensorSections s t))
      = Scheme.Modules.Hom.app (δ (Modules.pullback f) L M) (f ⁻¹ᵁ V)
          (Scheme.Modules.Hom.app ((Modules.pullback f).map ((adj Y).counit.app L ⊗ₘ (adj Y).counit.app M))
              (f ⁻¹ᵁ V)
            (Scheme.Modules.Hom.app ((Modules.pullback f).map
                (δ (Modules.sheafify Y) ((ι Y).obj L) ((ι Y).obj M))) (f ⁻¹ᵁ V)
              (pullbackLocalSection f (shUnit ((ι Y).obj L ⊗ (ι Y).obj M) V
                ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y, V)] (t : M.val.obj (op V))))))) := by
        rw [tensorSections_eq, cmpIso_hom]
        have a1 := pullbackLocalSection_app f ((adj Y).counit.app L ⊗ₘ (adj Y).counit.app M)
          (Scheme.Modules.Hom.app (δ (Modules.sheafify Y) ((ι Y).obj L) ((ι Y).obj M)) V
            (shUnit ((ι Y).obj L ⊗ (ι Y).obj M) V
              ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y, V)] (t : M.val.obj (op V)))))
        have a2 := pullbackLocalSection_app f (δ (Modules.sheafify Y) ((ι Y).obj L) ((ι Y).obj M))
          (shUnit ((ι Y).obj L ⊗ (ι Y).obj M) V
            ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y, V)] (t : M.val.obj (op V))))
        change (pullbackTensorObjIso f L M).hom.app (f ⁻¹ᵁ V) (pullbackLocalSection f
          (Scheme.Modules.Hom.app ((adj Y).counit.app L ⊗ₘ (adj Y).counit.app M) V
            (Scheme.Modules.Hom.app (δ (Modules.sheafify Y) ((ι Y).obj L) ((ι Y).obj M)) V
              (shUnit ((ι Y).obj L ⊗ (ι Y).obj M) V
                ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y, V)] (t : M.val.obj (op V))))))) = _
        refine (congrArg (fun w => (pullbackTensorObjIso f L M).hom.app (f ⁻¹ᵁ V) w)
          (a1.trans (congrArg (fun w => Scheme.Modules.Hom.app
            ((Modules.pullback f).map ((adj Y).counit.app L ⊗ₘ (adj Y).counit.app M)) (f ⁻¹ᵁ V) w) a2))).trans ?_
        rfl
    _ = Scheme.Modules.Hom.app ((Modules.pullback f).map ((adj Y).counit.app L) ⊗ₘ
            (Modules.pullback f).map ((adj Y).counit.app M)) (f ⁻¹ᵁ V)
          (Scheme.Modules.Hom.app (δ (Modules.pullback f) _ _) (f ⁻¹ᵁ V)
            (Scheme.Modules.Hom.app ((Modules.pullback f).map
                (δ (Modules.sheafify Y) ((ι Y).obj L) ((ι Y).obj M))) (f ⁻¹ᵁ V)
              (pullbackLocalSection f (shUnit ((ι Y).obj L ⊗ (ι Y).obj M) V
                ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y, V)] (t : M.val.obj (op V))))))) :=
        (congr($(hnat.symm).app (f ⁻¹ᵁ V) _) :)
    _ = Scheme.Modules.Hom.app ((Modules.pullback f).map ((adj Y).counit.app L) ⊗ₘ
            (Modules.pullback f).map ((adj Y).counit.app M)) (f ⁻¹ᵁ V)
          (Scheme.Modules.Hom.app (δ (Modules.sheafify Y ⋙ Modules.pullback f) ((ι Y).obj L) ((ι Y).obj M))
              (f ⁻¹ᵁ V)
            (pullbackLocalSection f (shUnit ((ι Y).obj L ⊗ (ι Y).obj M) V
              ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y, V)] (t : M.val.obj (op V)))))) := by
        rw [Functor.OplaxMonoidal.comp_δ]
        rfl
    _ = Scheme.Modules.Hom.app ((Modules.pullback f).map ((adj Y).counit.app L) ⊗ₘ
            (Modules.pullback f).map ((adj Y).counit.app M)) (f ⁻¹ᵁ V)
          (Modules.tensorSections (pullbackLocalSection f (shUnit ((ι Y).obj L) V s))
            (pullbackLocalSection f (shUnit ((ι Y).obj M) V t))) := by rw [key]
    _ = Modules.tensorSections (pullbackLocalSection f s) (pullbackLocalSection f t) := by
        erw [tensorHom_app_tensorSections_inl]
        rw [← pullbackLocalSection_app, ← pullbackLocalSection_app]
        erw [counit_app_shUnit, counit_app_shUnit]

end PullbackTensorSections

end AlgebraicGeometry.Scheme.Modules

end

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackTensorObjIso_hom_app_pullbackLocalSection_monoidalV2.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackTensorObjIso_hom_app_pullbackLocalSection_monoidalV2.AlgebraicGeometry.Scheme.Modules in

theorem solution {X Y : AlgebraicGeometry.Scheme.{u}} (φ : X ⟶ Y) {L M : Y.Modules} {U : Y.Opens}
    (s : Γ(L, U)) (t : Γ(M, U)) :
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso φ L M).hom.app (φ ⁻¹ᵁ U)
        (AlgebraicGeometry.Scheme.Modules.pullbackLocalSection φ (AlgebraicGeometry.Scheme.Modules.tensorSections s t)) =
      AlgebraicGeometry.Scheme.Modules.tensorSections (AlgebraicGeometry.Scheme.Modules.pullbackLocalSection φ s)
        (AlgebraicGeometry.Scheme.Modules.pullbackLocalSection φ t) :=
  PullbackTensorSections.pullbackTensorObjIso_hom_app_pullbackLocalSection_tensorSections φ L M U s t

end S_AlgebraicGeometry_Scheme_Modules_pullbackTensorObjIso_hom_app_pullbackLocalSection_monoidalV2
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackTensorObjIso_hom_app_pullbackLocalSection_monoidalV2 (solution)
