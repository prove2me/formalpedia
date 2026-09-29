-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.isIso_pullback_map_projectionMorphism_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/af1d3739-5479-5a28-8ef0-3b76d0ee92e7

import Mathlib
import Definitions.Def_PresheafOfModules_InternalHom
import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_PresheafOfModules_PullbackMonoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_sheafify_mu_app_tensorSections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_tensorHom_app_tensorSections
import Definitions.Def_AlgebraicGeometry_ModulesProjectionMorphism
import Definitions.Def_AlgebraicGeometry_ModulesBaseChangeHom
import Definitions.Def_AlgebraicGeometry_ModulesIhomSections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_isOpenImmersion
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullback_map_projectionMorphism_comp_counit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_whiskerRight_app_tensorSections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_leftUnitor_hom_app_tensorSections
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_pullback_map_projectionMorphism_iff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_pullback_map_projectionMorphism_iff.AlgebraicGeometry Opposite TensorProduct"
p2m_open "CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul Scheme.Modules.pushforward morphismRestrict_ι Scheme.Modules.pullback Scheme.Hom Scheme.Modules.Hom.comp_app Scheme.Modules.Hom isPullback_morphismRestrict Scheme Scheme.Modules.Hom.id_app Scheme.Modules.Hom.app Scheme.Modules.pullbackPushforwardAdjunction Scheme.Modules Scheme.Hom.comp_preimage Scheme.Modules.map_smul Scheme.Modules.projectionMorphism"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul ringCatSheaf Modules.pushforward Modules.pullback Hom.id_app Hom Γ Modules.Hom.comp_app Hom.app Modules.Hom Modules.Hom.id_app Modules.Hom.app Hom.comp_app Modules.pullbackPushforwardAdjunction Modules Opens Hom.comp_preimage grothendieckTopology Modules.map_smul PresheafOfModules Modules.sheafify Modules.tensorSections Modules.unitSection Modules.sheafify_mu_app_tensorSections Modules.tensorHom_app_tensorSections Modules.projectionMorphism"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "Hom.app_smul pushforward pullback presheaf Hom.comp_app Hom Hom.id_app Hom.app pullbackCongr pullbackPushforwardAdjunction map_smul pullbackComp tensor sheafify tensorIsoSheafify pullback₀ pullbackTensorObjIso pullbackTensorUnitObjIso tensorSections unitSection pullbackLocalSection pullbackLocalSection_smul pullbackLocalSection_app app_pullbackLocalSection counit_app_pullbackLocalSection pullback_hom_ext sheafify_mu_app_tensorSections tensorHom_app_tensorSections projectionMorphismMate projectionMorphism projectionMorphism_def projectionMorphismMate_def baseChangeHom conjugateEquiv_pullbackComp_hom unit_app_app_comp_baseChangeHom_app toPMod tensor_hom_ext isIso_baseChangeHom_of_isOpenImmersion whiskerRight_app_tensorSections leftUnitor_hom_app_tensorSections"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace PullbackTensorSections

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

private abbrev _root_.AlgebraicGeometry.Scheme.Modules.PullbackTensorSections.adj (Z : Scheme.{u}) := SheafOfModules.sheafifyAdj Z.sheaf.obj Z.ringCatSheaf.property
p2m_export "AlgebraicGeometry.Scheme.Modules.PullbackTensorSections" "adj"

private abbrev _root_.AlgebraicGeometry.Scheme.Modules.PullbackTensorSections.ι (Z : Scheme.{u}) := SheafOfModules.toPMod Z.sheaf.obj Z.ringCatSheaf.property
p2m_export "AlgebraicGeometry.Scheme.Modules.PullbackTensorSections" "ι"

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

lemma sheafify_δ_app_shUnit_tmul (A B : X.PresheafOfModules) (W : X.Opens) (a : A.obj (op W)) (b : B.obj (op W)) :
    (δ (Modules.sheafify X) A B).app W (shUnit (A ⊗ B) W (a ⊗ₜ[Γ(X, W)] b)) =
      Modules.tensorSections (L := (Modules.sheafify X).obj A) (M := (Modules.sheafify X).obj B)
        (shUnit A W a) (shUnit B W b) := by
  have h := Modules.sheafify_mu_app_tensorSections A B a b
  have h2 := congr($(Functor.Monoidal.μ_δ (Modules.sheafify X) A B).app W
    (Modules.tensorSections (L := (Modules.sheafify X).obj A) (M := (Modules.sheafify X).obj B)
      (shUnit A W a) (shUnit B W b)))
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app] at h2
  change (δ (Modules.sheafify X) A B).app W ((μ (Modules.sheafify X) A B).app W _) = _ at h2
  erw [h] at h2
  exact h2

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

def cmpIso (L M : Y.Modules) : (Modules.sheafify Y).obj ((ι Y).obj L ⊗ (ι Y).obj M) ≅ L ⊗ M :=
  (Functor.Monoidal.μIso (Modules.sheafify Y) ((ι Y).obj L) ((ι Y).obj M)).symm ≪≫
    ((asIso (adj Y).counit).app L ⊗ᵢ (asIso (adj Y).counit).app M)

lemma cmpIso_hom (L M : Y.Modules) :
    (cmpIso L M).hom = δ (Modules.sheafify Y) ((ι Y).obj L) ((ι Y).obj M) ≫
      ((adj Y).counit.app L ⊗ₘ (adj Y).counit.app M) := rfl

lemma tensorSections_eq (L M : Y.Modules) (V : Y.Opens) (s : Γ(L, V)) (t : Γ(M, V)) :
    Modules.tensorSections s t = Scheme.Modules.Hom.app (cmpIso L M).hom V
      (shUnit ((ι Y).obj L ⊗ (ι Y).obj M) V ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y, V)] (t : M.val.obj (op V)))) := rfl

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
    erw [Modules.tensorHom_app_tensorSections]
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
        erw [Modules.tensorHom_app_tensorSections]
        rw [← pullbackLocalSection_app, ← pullbackLocalSection_app]
        erw [counit_app_shUnit, counit_app_shUnit]

lemma pf_ε_app (V : Y.Opens) (g : (𝟙_ Y.PresheafOfModules).obj (op V)) :
    (ε (pf f)).app (op V) g = (f.app V (show Γ(Y, V) from g) :
      ((pf f).obj (𝟙_ X.PresheafOfModules)).obj (op V)) := by
  change (ε (PresheafOfModules.restrictScalars
      (PresheafOfModules.ringCatHom (R := (TopologicalSpace.Opens.map f.base).op ⋙ X.sheaf.obj) f.c)) ≫
    (PresheafOfModules.restrictScalars
      (PresheafOfModules.ringCatHom (R := (TopologicalSpace.Opens.map f.base).op ⋙ X.sheaf.obj) f.c)).map
        (ε (PresheafOfModules.pushforward₀OfCommRingCat (TopologicalSpace.Opens.map f.base) X.sheaf.obj))).app
      (op V) g = _
  rw [show ε (PresheafOfModules.pushforward₀OfCommRingCat (TopologicalSpace.Opens.map f.base) X.sheaf.obj)
      = 𝟙 _ from rfl, CategoryTheory.Functor.map_id, Category.comp_id]
  erw [ModuleCat.restrictScalars_η]
  rfl

lemma pb₀_η_app_pb₀Section (V : Y.Opens) (g : (𝟙_ Y.PresheafOfModules).obj (op V)) :
    (η (pullback₀ f)).app (op (f ⁻¹ᵁ V)) (pb₀Section f (𝟙_ Y.PresheafOfModules) V g)
      = (f.app V (show Γ(Y, V) from g) : (𝟙_ X.PresheafOfModules).obj (op (f ⁻¹ᵁ V))) := by
  have h : η (pullback₀ f) = ((adj₀ f).homEquiv _ _).symm (ε (pf f)) :=
    Adjunction.leftAdjointOplaxMonoidal_η (adj₀ f)
  rw [h]
  erw [homEquiv_symm_app_pb₀Section f (ε (pf f)) V g]
  exact pf_ε_app f V g

lemma pb₀_ε_app (V : Y.Opens) (g : (𝟙_ Y.PresheafOfModules).obj (op V)) :
    (ε (pullback₀ f)).app (op (f ⁻¹ᵁ V)) (f.app V (show Γ(Y, V) from g) : (𝟙_ X.PresheafOfModules).obj (op (f ⁻¹ᵁ V)))
      = pb₀Section f (𝟙_ Y.PresheafOfModules) V g := by
  have h1 := pb₀_η_app_pb₀Section f V g
  have h2 := congr($(Functor.Monoidal.η_ε (pullback₀ f)).app (op (f ⁻¹ᵁ V))
    (pb₀Section f (𝟙_ Y.PresheafOfModules) V g))
  change (ε (pullback₀ f)).app (op (f ⁻¹ᵁ V))
      ((η (pullback₀ f)).app (op (f ⁻¹ᵁ V)) (pb₀Section f (𝟙_ Y.PresheafOfModules) V g))
    = pb₀Section f (𝟙_ Y.PresheafOfModules) V g at h2
  rw [h1] at h2
  exact h2

lemma sheafify_ε_app {Z : Scheme.{u}} (W : Z.Opens) (c : Γ(𝟙_ Z.Modules, W)) :
    Scheme.Modules.Hom.app (ε (Modules.sheafify Z)) W c = shUnit (𝟙_ Z.PresheafOfModules) W c := by
  have h1 : Scheme.Modules.Hom.app (η (Modules.sheafify Z)) W (shUnit (𝟙_ Z.PresheafOfModules) W c) = c :=
    counit_app_shUnit (𝟙_ Z.Modules) W c
  have h2 := congr($(Functor.Monoidal.η_ε (Modules.sheafify Z)).app W (shUnit (𝟙_ Z.PresheafOfModules) W c))
  change Scheme.Modules.Hom.app (ε (Modules.sheafify Z)) W
      (Scheme.Modules.Hom.app (η (Modules.sheafify Z)) W (shUnit (𝟙_ Z.PresheafOfModules) W c))
    = shUnit (𝟙_ Z.PresheafOfModules) W c at h2
  rw [h1] at h2
  exact h2

set_option maxHeartbeats 3200000 in

lemma pullback_ε_app_unitSection (V : Y.Opens) :
    Scheme.Modules.Hom.app (ε (Modules.pullback f)) (f ⁻¹ᵁ V) (Modules.unitSection (f ⁻¹ᵁ V))
      = pullbackLocalSection f (Modules.unitSection V) := by
  letI := SheafOfModules.presheafW_isMonoidal Y.sheaf.obj Y.ringCatSheaf.property
  have hε := Localization.Monoidal.functorMonoidalOfComp_ε (Modules.sheafify Y)
    (SheafOfModules.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj)
    (Modules.pullback f) (pullback₀ f ⋙ Modules.sheafify X)

  rw [hε, Functor.LaxMonoidal.comp_ε]
  change Scheme.Modules.Hom.app ((Modules.pullback f).map (η (Modules.sheafify Y))) (f ⁻¹ᵁ V)
    (Scheme.Modules.Hom.app ((e f).inv.app (𝟙_ Y.PresheafOfModules)) (f ⁻¹ᵁ V)
      (Scheme.Modules.Hom.app ((Modules.sheafify X).map (ε (pullback₀ f))) (f ⁻¹ᵁ V)
        (Scheme.Modules.Hom.app (ε (Modules.sheafify X)) (f ⁻¹ᵁ V) (Modules.unitSection (f ⁻¹ᵁ V))))) = _
  rw [sheafify_ε_app]
  have hmap : Scheme.Modules.Hom.app ((Modules.sheafify X).map (ε (pullback₀ f))) (f ⁻¹ᵁ V)
      (shUnit (𝟙_ X.PresheafOfModules) (f ⁻¹ᵁ V) (Modules.unitSection (f ⁻¹ᵁ V)))
      = shUnit ((pullback₀ f).obj (𝟙_ Y.PresheafOfModules)) (f ⁻¹ᵁ V)
          ((ε (pullback₀ f)).app (op (f ⁻¹ᵁ V))
            (show (𝟙_ X.PresheafOfModules).obj (op (f ⁻¹ᵁ V)) from Modules.unitSection (f ⁻¹ᵁ V))) :=
    sheafify_map_app_shUnit (ε (pullback₀ f)) (f ⁻¹ᵁ V) _
  have h1 : (ε (pullback₀ f)).app (op (f ⁻¹ᵁ V))
      (show (𝟙_ X.PresheafOfModules).obj (op (f ⁻¹ᵁ V)) from Modules.unitSection (f ⁻¹ᵁ V))
        = pb₀Section f (𝟙_ Y.PresheafOfModules) V (Modules.unitSection V) := by
    rw [← pb₀_ε_app]
    congr 1
    exact ((f.app V).hom.map_one).symm
  rw [hmap, h1, e_inv_app_shUnit, ← pullbackLocalSection_app]
  congr 1
  exact counit_app_shUnit (𝟙_ Y.Modules) V (Modules.unitSection V)

theorem pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection (V : Y.Opens) :
    (pullbackTensorUnitObjIso f).hom.app (f ⁻¹ᵁ V) (pullbackLocalSection f (Modules.unitSection V))
      = Modules.unitSection (f ⁻¹ᵁ V) := by
  rw [← pullback_ε_app_unitSection]
  change Scheme.Modules.Hom.app (ε (Modules.pullback f) ≫ (Functor.Monoidal.εIso (Modules.pullback f)).inv)
    (f ⁻¹ᵁ V) (Modules.unitSection (f ⁻¹ᵁ V)) = _
  rw [Functor.Monoidal.εIso_inv, Functor.Monoidal.ε_η]
  rfl

theorem pullbackTensorUnitObjIso_hom_app_pullbackLocalSection' (V : Y.Opens) (g : Γ(𝟙_ Y.Modules, V)) :
    ((pullbackTensorUnitObjIso f).hom.app (f ⁻¹ᵁ V)) (pullbackLocalSection f g) =
      (show Γ(𝟙_ X.Modules, f ⁻¹ᵁ V) from f.app V (show Γ(Y, V) from g)) := by
  have hg : (show Γ(Y, V) from g) • Modules.unitSection V = g := by
    change (show Γ(Y, V) from g) * 1 = (show Γ(Y, V) from g)
    exact mul_one _
  have key : ((pullbackTensorUnitObjIso f).hom.app (f ⁻¹ᵁ V))
      (pullbackLocalSection f ((show Γ(Y, V) from g) • Modules.unitSection V)) =
        (show Γ(𝟙_ X.Modules, f ⁻¹ᵁ V) from f.app V (show Γ(Y, V) from g)) := by
    rw [pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul,
      pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection]
    change f.app V (show Γ(Y, V) from g) * 1 = _
    rw [mul_one]
    all_goals rfl
  rw [hg] at key
  exact key

end PullbackTensorSections

end AlgebraicGeometry.Scheme.Modules

open TopologicalSpace
p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_pullback_map_projectionMorphism_iff.AlgebraicGeometry.Scheme.Modules"

namespace Ws31Restrict

variable {W X Y Z : Scheme.{u}}

private theorem _root_.Ws31Restrict.pullbackTensorObjIso_hom_app_pullbackLocalSection_tensorSections (f : X ⟶ Y) (L M : Y.Modules)
    (V : Y.Opens) (s : Γ(L, V)) (t : Γ(M, V)) :
    ((pullbackTensorObjIso f L M).hom.app (f ⁻¹ᵁ V)) (pullbackLocalSection f (tensorSections s t))
      = tensorSections (pullbackLocalSection f s) (pullbackLocalSection f t) :=
  AlgebraicGeometry.Scheme.Modules.PullbackTensorSections.pullbackTensorObjIso_hom_app_pullbackLocalSection_tensorSections
    f L M V s t

p2m_export "Ws31Restrict" "pullbackTensorObjIso_hom_app_pullbackLocalSection_tensorSections"
theorem pullbackTensorUnitObjIso_hom_app_pullbackLocalSection (f : X ⟶ Y) (V : Y.Opens) (g : Γ(𝟙_ Y.Modules, V)) :
    ((pullbackTensorUnitObjIso f).hom.app (f ⁻¹ᵁ V)) (pullbackLocalSection f g)
      = (f.app V (g : Γ(Y, V)) : Γ(𝟙_ X.Modules, f ⁻¹ᵁ V)) :=
  AlgebraicGeometry.Scheme.Modules.PullbackTensorSections.pullbackTensorUnitObjIso_hom_app_pullbackLocalSection' f V g

theorem projectionMorphism_app_tensorSections (i : Z ⟶ X) (F : X.Modules) (V : X.Opens)
    (a : Γ((Scheme.Modules.pushforward i).obj (𝟙_ Z.Modules), V)) (s : Γ(F, V)) :
    (projectionMorphism i F).app V (tensorSections a s)
      = (((show Γ(Z, i ⁻¹ᵁ V) from a) • pullbackLocalSection i s : Γ((Scheme.Modules.pullback i).obj F, i ⁻¹ᵁ V))
          : Γ((Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj F), V)) := by
  rw [projectionMorphism_def, Adjunction.homEquiv_unit]
  change (projectionMorphismMate i F).app (i ⁻¹ᵁ V) (pullbackLocalSection i (tensorSections a s)) = _
  rw [projectionMorphismMate_def]
  change (λ_ ((Scheme.Modules.pullback i).obj F)).hom.app _
      ((((Scheme.Modules.pullbackPushforwardAdjunction i).counit.app (𝟙_ Z.Modules)) ▷
          (Scheme.Modules.pullback i).obj F).app _
        ((Functor.Monoidal.μIso (Scheme.Modules.pullback i)
            ((Scheme.Modules.pushforward i).obj (𝟙_ Z.Modules)) F).inv.app _
          (pullbackLocalSection i (tensorSections a s)))) = _
  have hB1 : (Functor.Monoidal.μIso (Scheme.Modules.pullback i)
        ((Scheme.Modules.pushforward i).obj (𝟙_ Z.Modules)) F).inv.app (i ⁻¹ᵁ V)
        (pullbackLocalSection i (tensorSections a s))
      = tensorSections (pullbackLocalSection i a) (pullbackLocalSection i s) :=
    pullbackTensorObjIso_hom_app_pullbackLocalSection_tensorSections i _ F V a s
  rw [hB1, whiskerRight_app_tensorSections, counit_app_pullbackLocalSection, leftUnitor_hom_app_tensorSections]

theorem app_naturality {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (k : V ⟶ U) (m : Γ(M, U)) :
    φ.app V (M.presheaf.map k.op m) = N.presheaf.map k.op (φ.app U m) :=
  PresheafOfModules.naturality_apply φ.val k.op m

theorem pullbackComp_hom_app_app_pullbackLocalSection (f : W ⟶ X) (g : X ⟶ Y) (L : Y.Modules) (V : Y.Opens)
    (s : Γ(L, V)) :
    (((pullbackComp f g).hom.app L).app (f ⁻¹ᵁ g ⁻¹ᵁ V)) (pullbackLocalSection f (pullbackLocalSection g s))
      = pullbackLocalSection (f ≫ g) s := by
  have h := unit_conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp (Scheme.Modules.pullbackPushforwardAdjunction f))
    (pullbackComp f g).hom L
  rw [conjugateEquiv_pullbackComp_hom, Adjunction.comp_unit_app] at h
  have h' := congrArg (fun k => Scheme.Modules.Hom.app k V s) h
  exact h'.symm

theorem pullbackCongr_hom_app_app_pullbackLocalSection {f g : X ⟶ Y} (e : f = g) (L : Y.Modules) (V : Y.Opens)
    (s : Γ(L, V)) :
    (((pullbackCongr e).hom.app L).app (f ⁻¹ᵁ V)) (pullbackLocalSection f s)
      = ((Scheme.Modules.pullback g).obj L).presheaf.map (eqToHom (by rw [e])).op (pullbackLocalSection g s) := by
  subst e
  simp [pullbackCongr]

section main
variable (i : Z ⟶ X) (F : X.Modules) (U : X.Opens)

theorem sq : (i ⁻¹ᵁ U).ι ≫ i = (i ∣_ U) ≫ U.ι := (morphismRestrict_ι i U).symm

theorem preimage_eq (V : X.Opens) : (i ∣_ U) ⁻¹ᵁ U.ι ⁻¹ᵁ V = (i ⁻¹ᵁ U).ι ⁻¹ᵁ i ⁻¹ᵁ V := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, sq]

theorem isIso_bc (N : Z.Modules) : IsIso (baseChangeHom (sq i U) N) :=
  isIso_baseChangeHom_of_isOpenImmersion (isPullback_morphismRestrict i U).flip N

theorem bc_app_pullbackLocalSection (N : Z.Modules) (V : X.Opens)
    (t : Γ((Scheme.Modules.pushforward i).obj N, V)) :
    (baseChangeHom (sq i U) N).app (U.ι ⁻¹ᵁ V) (pullbackLocalSection U.ι t)
      = ((Scheme.Modules.pullback (i ⁻¹ᵁ U).ι).obj N).presheaf.map (eqToHom (preimage_eq i U V)).op
          (pullbackLocalSection (i ⁻¹ᵁ U).ι (t : Γ(N, i ⁻¹ᵁ V))) := by
  have h := unit_app_app_comp_baseChangeHom_app i U.ι (i ∣_ U) (i ⁻¹ᵁ U).ι (sq i U) N V
  exact CategoryTheory.ConcreteCategory.congr_hom h t

noncomputable def τIso :
    (Scheme.Modules.pullback (i ∣_ U)).obj ((Scheme.Modules.pullback U.ι).obj F) ≅
      (Scheme.Modules.pullback (i ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback i).obj F) :=
  (pullbackComp (i ∣_ U) U.ι).app F ≪≫ (pullbackCongr (sq i U).symm).app F ≪≫
    ((pullbackComp (i ⁻¹ᵁ U).ι i).app F).symm

theorem τIso_hom_app_pullbackLocalSection (V : X.Opens) (s : Γ(F, V)) :
    (τIso i F U).hom.app _ (pullbackLocalSection (i ∣_ U) (pullbackLocalSection U.ι s))
      = ((Scheme.Modules.pullback (i ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback i).obj F)).presheaf.map
          (eqToHom (preimage_eq i U V)).op (pullbackLocalSection (i ⁻¹ᵁ U).ι (pullbackLocalSection i s)) := by
  have h1 := pullbackComp_hom_app_app_pullbackLocalSection (i ∣_ U) U.ι F V s
  have h2 := pullbackCongr_hom_app_app_pullbackLocalSection (sq i U).symm F V s
  have h3 := pullbackComp_hom_app_app_pullbackLocalSection (i ⁻¹ᵁ U).ι i F V s

  have hid := CategoryTheory.ConcreteCategory.congr_hom
    (congrArg (fun k => Scheme.Modules.Hom.app k ((i ⁻¹ᵁ U).ι ⁻¹ᵁ i ⁻¹ᵁ V))
      ((pullbackComp (i ⁻¹ᵁ U).ι i).hom_inv_id_app F))
    (pullbackLocalSection (i ⁻¹ᵁ U).ι (pullbackLocalSection i s))
  have h3' : ((pullbackComp (i ⁻¹ᵁ U).ι i).inv.app F).app ((i ⁻¹ᵁ U).ι ⁻¹ᵁ i ⁻¹ᵁ V)
      (pullbackLocalSection ((i ⁻¹ᵁ U).ι ≫ i) s) = pullbackLocalSection (i ⁻¹ᵁ U).ι (pullbackLocalSection i s) := by
    rw [← h3]
    exact hid

  change ((pullbackComp (i ⁻¹ᵁ U).ι i).inv.app F).app _
      (((pullbackCongr (sq i U).symm).hom.app F).app _
        (((pullbackComp (i ∣_ U) U.ι).hom.app F).app _ (pullbackLocalSection (i ∣_ U) (pullbackLocalSection U.ι s)))) = _
  rw [h1]
  erw [h2, app_naturality, h3']
  all_goals rfl

noncomputable def βIso :
    (Scheme.Modules.pullback U.ι).obj ((Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj F)) ≅
      (Scheme.Modules.pushforward (i ∣_ U)).obj
        ((Scheme.Modules.pullback (i ∣_ U)).obj ((Scheme.Modules.pullback U.ι).obj F)) :=
  haveI := isIso_bc i U ((Scheme.Modules.pullback i).obj F)
  asIso (baseChangeHom (sq i U) ((Scheme.Modules.pullback i).obj F)) ≪≫
    (Scheme.Modules.pushforward (i ∣_ U)).mapIso (τIso i F U).symm

noncomputable def unitBC :
    (Scheme.Modules.pullback U.ι).obj ((Scheme.Modules.pushforward i).obj (𝟙_ Z.Modules)) ≅
      (Scheme.Modules.pushforward (i ∣_ U)).obj (𝟙_ _) :=
  haveI := isIso_bc i U (𝟙_ Z.Modules)
  asIso (baseChangeHom (sq i U) (𝟙_ Z.Modules)) ≪≫
    (Scheme.Modules.pushforward (i ∣_ U)).mapIso (pullbackTensorUnitObjIso (i ⁻¹ᵁ U).ι)

noncomputable def αIso :
    (Scheme.Modules.pullback U.ι).obj ((Scheme.Modules.pushforward i).obj (𝟙_ Z.Modules) ⊗ F) ≅
      (Scheme.Modules.pushforward (i ∣_ U)).obj (𝟙_ _) ⊗ (Scheme.Modules.pullback U.ι).obj F :=
  pullbackTensorObjIso U.ι _ F ≪≫ whiskerRightIso (unitBC i U) _

noncomputable def nf (V : X.Opens) (a : Γ((Scheme.Modules.pushforward i).obj (𝟙_ Z.Modules), V)) (s : Γ(F, V)) :
    Γ((Scheme.Modules.pullback (i ∣_ U)).obj ((Scheme.Modules.pullback U.ι).obj F), (i ∣_ U) ⁻¹ᵁ U.ι ⁻¹ᵁ V) :=
  (show Γ(↑(i ⁻¹ᵁ U), (i ∣_ U) ⁻¹ᵁ U.ι ⁻¹ᵁ V) from
      (i ⁻¹ᵁ U).toScheme.presheaf.map (eqToHom (preimage_eq i U V)).op
        ((i ⁻¹ᵁ U).ι.app (i ⁻¹ᵁ V) (show Γ(Z, i ⁻¹ᵁ V) from a))) •
    pullbackLocalSection (i ∣_ U) (pullbackLocalSection U.ι s)

theorem key_lhs (V : X.Opens) (a : Γ((Scheme.Modules.pushforward i).obj (𝟙_ Z.Modules), V)) (s : Γ(F, V)) :
    ((Scheme.Modules.pullback U.ι).map (projectionMorphism i F) ≫ (βIso i F U).hom).app (U.ι ⁻¹ᵁ V)
        (pullbackLocalSection U.ι (tensorSections a s))
      = (nf i F U V a s : Γ((Scheme.Modules.pushforward (i ∣_ U)).obj
          ((Scheme.Modules.pullback (i ∣_ U)).obj ((Scheme.Modules.pullback U.ι).obj F)), U.ι ⁻¹ᵁ V)) := by
  haveI := isIso_bc i U ((Scheme.Modules.pullback i).obj F)

  change (τIso i F U).inv.app _ ((baseChangeHom (sq i U) ((Scheme.Modules.pullback i).obj F)).app _
    (((Scheme.Modules.pullback U.ι).map (projectionMorphism i F)).app _ (pullbackLocalSection U.ι (tensorSections a s)))) = _
  rw [← pullbackLocalSection_app, projectionMorphism_app_tensorSections]
  erw [bc_app_pullbackLocalSection i U ((Scheme.Modules.pullback i).obj F) V]
  rw [pullbackLocalSection_smul, Scheme.Modules.map_smul, Scheme.Modules.Hom.app_smul]

  have hτ := τIso_hom_app_pullbackLocalSection i F U V s
  have hid := CategoryTheory.ConcreteCategory.congr_hom
    (congrArg (fun k => Scheme.Modules.Hom.app k ((i ∣_ U) ⁻¹ᵁ U.ι ⁻¹ᵁ V)) ((τIso i F U).hom_inv_id))
    (pullbackLocalSection (i ∣_ U) (pullbackLocalSection U.ι s))
  have hinv : (τIso i F U).inv.app _
      (((Scheme.Modules.pullback (i ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback i).obj F)).presheaf.map
          (eqToHom (preimage_eq i U V)).op (pullbackLocalSection (i ⁻¹ᵁ U).ι (pullbackLocalSection i s)))
      = pullbackLocalSection (i ∣_ U) (pullbackLocalSection U.ι s) := by
    rw [← hτ]
    exact hid
  erw [hinv]
  all_goals rfl

theorem key_rhs (V : X.Opens) (a : Γ((Scheme.Modules.pushforward i).obj (𝟙_ Z.Modules), V)) (s : Γ(F, V)) :
    ((αIso i F U).hom ≫ projectionMorphism (i ∣_ U) ((Scheme.Modules.pullback U.ι).obj F)).app (U.ι ⁻¹ᵁ V)
        (pullbackLocalSection U.ι (tensorSections a s))
      = (nf i F U V a s : Γ((Scheme.Modules.pushforward (i ∣_ U)).obj
          ((Scheme.Modules.pullback (i ∣_ U)).obj ((Scheme.Modules.pullback U.ι).obj F)), U.ι ⁻¹ᵁ V)) := by
  haveI := isIso_bc i U (𝟙_ Z.Modules)
  change (projectionMorphism (i ∣_ U) ((Scheme.Modules.pullback U.ι).obj F)).app _
    (((unitBC i U).hom ▷ (Scheme.Modules.pullback U.ι).obj F).app _
      ((pullbackTensorObjIso U.ι ((Scheme.Modules.pushforward i).obj (𝟙_ Z.Modules)) F).hom.app _
        (pullbackLocalSection U.ι (tensorSections a s)))) = _
  rw [pullbackTensorObjIso_hom_app_pullbackLocalSection_tensorSections, whiskerRight_app_tensorSections]

  have hu : (unitBC i U).hom.app (U.ι ⁻¹ᵁ V) (pullbackLocalSection U.ι a)
      = (show Γ((Scheme.Modules.pushforward (i ∣_ U)).obj (𝟙_ _), U.ι ⁻¹ᵁ V) from
          (𝟙_ (↑(i ⁻¹ᵁ U) : Scheme.{u}).Modules).presheaf.map (eqToHom (preimage_eq i U V)).op
            ((show Γ(𝟙_ (↑(i ⁻¹ᵁ U) : Scheme.{u}).Modules, (i ⁻¹ᵁ U).ι ⁻¹ᵁ i ⁻¹ᵁ V) from
              (i ⁻¹ᵁ U).ι.app (i ⁻¹ᵁ V) (show Γ(Z, i ⁻¹ᵁ V) from a)))) := by
    change (pullbackTensorUnitObjIso (i ⁻¹ᵁ U).ι).hom.app _
      ((baseChangeHom (sq i U) (𝟙_ Z.Modules)).app _ (pullbackLocalSection U.ι a)) = _
    erw [bc_app_pullbackLocalSection i U (𝟙_ Z.Modules) V a]
    rw [app_naturality]
    erw [pullbackTensorUnitObjIso_hom_app_pullbackLocalSection]
    all_goals rfl
  rw [hu]
  erw [projectionMorphism_app_tensorSections]
  all_goals rfl

theorem key :
    (Scheme.Modules.pullback U.ι).map (projectionMorphism i F) ≫ (βIso i F U).hom
      = (αIso i F U).hom ≫ projectionMorphism (i ∣_ U) ((Scheme.Modules.pullback U.ι).obj F) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).homEquiv _ _).injective
  apply tensor_hom_ext
  intro V a s
  have e1 := app_pullbackLocalSection U.ι
    ((Scheme.Modules.pullback U.ι).map (projectionMorphism i F) ≫ (βIso i F U).hom) (tensorSections a s)
  have e2 := app_pullbackLocalSection U.ι
    ((αIso i F U).hom ≫ projectionMorphism (i ∣_ U) ((Scheme.Modules.pullback U.ι).obj F)) (tensorSections a s)
  rw [key_lhs] at e1
  rw [key_rhs] at e2
  exact e1.symm.trans e2

theorem main :
    IsIso ((Scheme.Modules.pullback U.ι).map (projectionMorphism i F)) ↔
      IsIso (projectionMorphism (i ∣_ U) ((Scheme.Modules.pullback U.ι).obj F)) := by
  have hk := key i F U
  constructor
  · intro h
    have e : projectionMorphism (i ∣_ U) ((Scheme.Modules.pullback U.ι).obj F)
        = (αIso i F U).inv ≫ ((Scheme.Modules.pullback U.ι).map (projectionMorphism i F) ≫ (βIso i F U).hom) := by
      rw [hk, Iso.inv_hom_id_assoc]
    have h1 : IsIso ((Scheme.Modules.pullback U.ι).map (projectionMorphism i F) ≫ (βIso i F U).hom) :=
      @IsIso.comp_isIso _ _ _ _ _ _ _ h (Iso.isIso_hom _)
    rw [e]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_inv _) h1
  · intro h
    have e : (Scheme.Modules.pullback U.ι).map (projectionMorphism i F)
        = ((αIso i F U).hom ≫ projectionMorphism (i ∣_ U) ((Scheme.Modules.pullback U.ι).obj F)) ≫
            (βIso i F U).inv := by
      rw [← hk, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have h1 : IsIso ((αIso i F U).hom ≫ projectionMorphism (i ∣_ U) ((Scheme.Modules.pullback U.ι).obj F)) :=
      @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_hom _) h
    rw [e]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 (Iso.isIso_inv _)

end main

end Ws31Restrict

theorem solution {Z X : Scheme.{u}} (i : Z ⟶ X) (F : X.Modules) (U : X.Opens) :
    IsIso ((Scheme.Modules.pullback U.ι).map (Scheme.Modules.projectionMorphism i F)) ↔
      IsIso (Scheme.Modules.projectionMorphism (i ∣_ U) ((Scheme.Modules.pullback U.ι).obj F)) :=
  Ws31Restrict.main i F U

end

end S_AlgebraicGeometry_Scheme_Modules_isIso_pullback_map_projectionMorphism_iff
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_pullback_map_projectionMorphism_iff (solution)
