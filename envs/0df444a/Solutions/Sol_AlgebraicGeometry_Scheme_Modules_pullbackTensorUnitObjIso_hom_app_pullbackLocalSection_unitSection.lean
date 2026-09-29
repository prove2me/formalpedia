-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/d231afea-6b3b-5625-ae4f-befbe1917906

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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection.AlgebraicGeometry Opposite TensorProduct"
p2m_open "CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Scheme Scheme.Modules.Hom.id_app Scheme.Modules.Hom.app Scheme.Modules Scheme.Modules.pullbackTensorUnitObjIso Scheme.Modules.unitSection Scheme.Modules.pullbackLocalSection"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul ringCatSheaf Modules.pullback Hom.id_app Hom Γ Modules.Hom.comp_app Hom.app Modules.Hom Modules.Hom.id_app Modules.Hom.app Hom.comp_app Modules Opens grothendieckTopology PresheafOfModules Modules.sheafify Modules.pullbackTensorUnitObjIso Modules.tensorSections Modules.unitSection Modules.pullbackLocalSection Modules.sheafify_mu_app_tensorSections"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "Hom.app_smul pullback presheaf Hom.comp_app Hom Hom.id_app Hom.app pullbackPushforwardAdjunction tensor sheafify pullback₀ pullbackTensorUnitObjIso tensorSections unitSection pullbackLocalSection pullbackLocalSection_smul pullbackLocalSection_app sheafify_mu_app_tensorSections"
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

end

theorem solution
    {X Y : AlgebraicGeometry.Scheme.{u}} (φ : X ⟶ Y) (U : Y.Opens) :
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorUnitObjIso φ).hom.app (φ ⁻¹ᵁ U)
      (AlgebraicGeometry.Scheme.Modules.pullbackLocalSection φ
        (AlgebraicGeometry.Scheme.Modules.unitSection U)) =
    AlgebraicGeometry.Scheme.Modules.unitSection (φ ⁻¹ᵁ U) :=
  AlgebraicGeometry.Scheme.Modules.PullbackTensorSections.pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection φ U

end S_AlgebraicGeometry_Scheme_Modules_pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection (solution)
