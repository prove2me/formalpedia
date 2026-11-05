-- Prove2me | Definitions.Def_SeshadriPrelim2
-- name    : SeshadriPrelim2
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T14:34:52.677197+00:00
-- url     : https://prove2.me/theorems/5a6a6d98-2f6b-42a8-8d9c-fbcf9417740c
-- title:
--   Maximal Seshadri constants: supporting development, part 2
-- statement:
--   Part 2 of 6 of the supporting Lean development for the maximal Seshadri constants theorem. It holds the definitions that the statements of the published child theorems refer to, in source order, together with the proved lemmas that their bodies and type class instances rely on. No result is assumed: every lemma here has a proof. Source modules: `Sheaves.Restriction`.
--
--   **Formalization Note** Definitions of this development carry proof fields, so their dependencies must be proved here rather than imported from theorems. The code is OpenAI's, carved from `lean/OAI/AlgebraicGeometry/Seshadri` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim1

set_option linter.all false

section
namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.ModulePresheaf
open PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F G : C ⥤ D} {T : Cᵒᵖ ⥤ RingCat.{u}} {S : Dᵒᵖ ⥤ RingCat.{u}}

def pushforwardCongr {φ ψ : T ⟶ F.op ⋙ S} (h : φ = ψ) :
    pushforward.{v} φ ≅ pushforward.{v} ψ :=
  NatIso.ofComponents (fun M ↦
    PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsCongr (by subst h; rfl)).app _)
      (fun _ _ _ ↦ by subst h; rfl)) (fun _ ↦ by subst h; rfl)

@[simp] lemma pushforwardCongr_hom_app {φ ψ : T ⟶ F.op ⋙ S} (h : φ = ψ)
    (M : PresheafOfModules.{v} S) (U) (x) :
    ((pushforwardCongr h).hom.app M).app U x = x := by
  subst h
  rfl

def pushforwardNatTrans (φ : T ⟶ G.op ⋙ S) (α : F ⟶ G) :
    pushforward.{v} φ ⟶
      pushforward.{v} (φ ≫ whiskerRight (NatTrans.op α) S) where
  app M := {
    app U := (ModuleCat.restrictScalars (φ.app U).hom).map (M.map (α.app U.unop).op)
    naturality {U V} i := by
      ext x
      change (M.presheaf.map (G.map i.unop).op ≫ M.presheaf.map (α.app V.unop).op) _ =
        (M.presheaf.map (α.app U.unop).op ≫ M.presheaf.map (F.map i.unop).op) _
      simp only [← Functor.map_comp, ← op_comp, α.naturality] }
  naturality {M N} f := by
    ext U x
    exact congr($(f.naturality (α.app U.unop).op) x).symm

@[simp] lemma pushforwardNatTrans_app_app
    (φ : T ⟶ G.op ⋙ S) (α : F ⟶ G) (M U x) :
    ((pushforwardNatTrans φ α).app M).app U x = M.map (α.app U.unop).op x := rfl

variable {F : C ⥤ D} {G : D ⥤ C}
  (adj : F ⊣ G) (φ : T ⟶ F.op ⋙ S) (ψ : S ⟶ G.op ⋙ T)
  (H₁ : whiskerRight (NatTrans.op adj.counit) S = ψ ≫ G.op.whiskerLeft φ)
  (H₂ : φ ≫ F.op.whiskerLeft ψ ≫
    whiskerRight (NatTrans.op adj.unit) T = 𝟙 T)

def pushforwardPushforwardAdj : pushforward.{v} φ ⊣ pushforward.{v} ψ where
  unit := (pushforwardId _).inv ≫ pushforwardNatTrans (𝟙 _) adj.counit ≫
    (pushforwardCongr (by simpa using H₁)).hom ≫ (pushforwardComp _ _).inv
  counit := (pushforwardComp _ _).hom ≫ pushforwardNatTrans _ adj.unit ≫
    (pushforwardCongr (by simpa using H₂)).hom ≫ (pushforwardId _).hom
  left_triangle_components M := by
    ext U x
    simp only [comp_app, ModuleCat.comp_apply,
      pushforwardId, pushforwardComp, Iso.refl_hom, Iso.refl_inv]
    change M.map (F.map (adj.unit.app U.unop)).op
      (M.map (adj.counit.app (F.obj U.unop)).op x) = x
    change M.obj (Opposite.op (F.obj U.unop)) at x
    erw [← M.map_comp_apply, ← op_comp, adj.left_triangle_components, op_id, M.map_id]
    rfl
  right_triangle_components M := by
    ext U x
    simp only [comp_app, ModuleCat.comp_apply,
      pushforwardId, pushforwardComp, Iso.refl_hom, Iso.refl_inv]
    change M.map (adj.unit.app (G.obj U.unop)).op
      (M.map (G.map (adj.counit.app U.unop)).op x) = x
    change M.obj (Opposite.op (G.obj U.unop)) at x
    erw [← M.map_comp_apply, ← op_comp, adj.right_triangle_components, op_id, M.map_id]
    rfl

end MaximalSeshadri.ModulePresheaf

namespace MaximalSeshadri.Geometry
open AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]

def modulePresheafRestrict : PresheafOfModules Y.ringCatSheaf.obj ⥤
    PresheafOfModules X.ringCatSheaf.obj :=
  let α : X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf :=
    { app U := (f.appIso U.unop).inv }
  PresheafOfModules.pushforward (Functor.whiskerRight α (forget₂ CommRingCat RingCat))

def modulePresheafRestrictAdjunction : modulePresheafRestrict f ⊣
    PresheafOfModules.pushforward f.toRingCatSheafHom.hom := by
  refine ModulePresheaf.pushforwardPushforwardAdj
    (by exact f.isOpenEmbedding.isOpenMap.adjunction) _ _ ?_ ?_
  · ext U x
    exact congr($((f.app_appIso_inv _).symm).hom x)
  · ext U x
    have h : (f.appIso U.unop).inv ≫ f.app _ ≫
        X.presheaf.map (eqToHom (f.preimage_image_eq U.unop).symm).op = 𝟙 _ := by
      rw [Scheme.Hom.appIso_inv_app_assoc, ← Functor.map_comp, ← X.presheaf.map_id]
      rfl
    exact congr($h x)

def moduleSheafificationRestrict :
    PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj) ⋙
      Scheme.Modules.restrictFunctor f ≅
    modulePresheafRestrict f ⋙
      PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj) :=
  Adjunction.leftAdjointUniq
    ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).comp
      (Scheme.Modules.restrictAdjunction f))
    ((modulePresheafRestrictAdjunction f).comp
      (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)))

end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open MonoidalCategory
variable {X : Scheme}

def modulePresheafRestrictOpensIso (U : X.Opens) :
    modulePresheafRestrict U.ι ≅
      PresheafOfModules.pushforward₀OfCommRingCat U.ι.opensFunctor X.presheaf := by
  let α : U.toScheme.presheaf ⟶ U.ι.opensFunctor.op ⋙ X.presheaf :=
    { app V := (U.ι.appIso V.unop).inv }
  have h : Functor.whiskerRight α (forget₂ CommRingCat RingCat) = 𝟙 _ := by
    ext V x
    simp only [Functor.whiskerRight_app, α, Scheme.Opens.ι_appIso, Iso.refl_inv]
    rfl
  exact ModulePresheaf.pushforwardCongr (F := U.ι.opensFunctor)
    (T := U.toScheme.ringCatSheaf.obj) (S := X.ringCatSheaf.obj) h

def modulePresheafTensorRestrict (U : X.Opens)
    (M N : PresheafOfModules X.ringCatSheaf.obj) :
    (modulePresheafRestrict U.ι).obj
        (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M N) ≅
      PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := U.toScheme.presheaf)
        ((modulePresheafRestrict U.ι).obj M)
        ((modulePresheafRestrict U.ι).obj N) := by
  letI : MonoidalCategory (PresheafOfModules U.toScheme.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := U.toScheme.presheaf)
  exact (modulePresheafRestrictOpensIso U).app _ ≪≫
    (Functor.Monoidal.μIso
      (PresheafOfModules.pushforward₀OfCommRingCat U.ι.opensFunctor X.presheaf) M N).symm ≪≫
    tensorIso ((modulePresheafRestrictOpensIso U).symm.app M)
      ((modulePresheafRestrictOpensIso U).symm.app N)

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry
variable {X : Scheme}

def moduleTensorRestrict (U : X.Opens) (M N : X.Modules) :
    (moduleTensor X M N).restrict U.ι ≅
      moduleTensor U.toScheme (M.restrict U.ι) (N.restrict U.ι) :=
  (moduleSheafificationRestrict U.ι).app _ ≪≫
    (PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)).mapIso
      (modulePresheafTensorRestrict U M.val N.val)

def moduleTensorIso {M N P Q : X.Modules} (e : M ≅ N) (f : P ≅ Q) :
    moduleTensor X M P ≅ moduleTensor X N Q := by
  letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (tensorIso ((SheafOfModules.forget _).mapIso e) ((SheafOfModules.forget _).mapIso f))

def moduleTensorUnit (M : X.Modules) :
    moduleTensor X (structureSheaf X) M ≅ M := by
  letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso (λ_ M.val) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).counit).app M

def modulePowFrame {M : X.Modules} (U : X.Opens)
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) :
    ∀ n, (modulePow X M n).restrict U.ι ≅ structureSheaf U.toScheme
  | 0 => Scheme.Modules.restrictUnitIso U.ι
  | n + 1 => moduleTensorRestrict U M (modulePow X M n) ≪≫
    moduleTensorIso e (modulePowFrame U e n) ≪≫ moduleTensorUnit _

def LineBundle.pow (L : LineBundle X) (n : ℕ) : LineBundle X where
  sheaf := modulePow X L.sheaf n
  locallyRankOne x := by
    obtain ⟨U, hx, ⟨frame⟩⟩ := L.locallyRankOne x
    exact ⟨U, hx, ⟨modulePowFrame U frame n⟩⟩

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry
variable {X : Scheme}

def moduleTensorMap {M N P Q : X.Modules} (f : M ⟶ N) (g : P ⟶ Q) :
    moduleTensor X M P ⟶ moduleTensor X N Q :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) f.val g.val)

@[simp] lemma moduleTensorMap_id (M N : X.Modules) :
    moduleTensorMap (𝟙 M) (𝟙 N) = 𝟙 (moduleTensor X M N) := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  change (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    ((𝟙 M.val) ⊗ₘ (𝟙 N.val)) = _
  rw [id_tensorHom_id]
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map_id _

@[reassoc] lemma moduleTensorMap_comp {M N P Q R T : X.Modules}
    (f : M ⟶ N) (g : N ⟶ P) (h : Q ⟶ R) (k : R ⟶ T) :
    moduleTensorMap (f ≫ g) (h ≫ k) = moduleTensorMap f h ≫ moduleTensorMap g k := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  change (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    ((f.val ≫ g.val) ⊗ₘ (h.val ≫ k.val)) = _
  rw [← tensorHom_comp_tensorHom]
  exact Functor.map_comp _ _ _

instance moduleTensorMap_isIso {M N P Q : X.Modules} (f : M ⟶ N)
    (g : P ⟶ Q) [IsIso f] [IsIso g] : IsIso (moduleTensorMap f g) := by
  refine ⟨⟨moduleTensorMap (inv f) (inv g), ?_, ?_⟩⟩ <;>
    rw [← moduleTensorMap_comp] <;> simp

def modulePowMap {M N : X.Modules} (f : M ⟶ N) :
    ∀ n, modulePow X M n ⟶ modulePow X N n
  | 0 => 𝟙 _
  | n + 1 => moduleTensorMap f (modulePowMap f n)

@[simp] lemma modulePowMap_id (M : X.Modules) (n : ℕ) :
    modulePowMap (𝟙 M) n = 𝟙 (modulePow X M n) := by
  induction n with
  | zero => rfl
  | succ n hn =>
    change moduleTensorMap (𝟙 M) (modulePowMap (𝟙 M) n) = 𝟙 (moduleTensor X M (modulePow X M n))
    rw [hn, moduleTensorMap_id]

@[reassoc] lemma modulePowMap_comp {M N P : X.Modules}
    (f : M ⟶ N) (g : N ⟶ P) (n : ℕ) :
    modulePowMap (f ≫ g) n = modulePowMap f n ≫ modulePowMap g n := by
  induction n with
  | zero => exact (Category.id_comp _).symm
  | succ n hn =>
    change moduleTensorMap (f ≫ g) (modulePowMap (f ≫ g) n) =
      moduleTensorMap f (modulePowMap f n) ≫ moduleTensorMap g (modulePowMap g n)
    rw [hn, moduleTensorMap_comp]

instance modulePowMap_isIso {M N : X.Modules} (f : M ⟶ N) [IsIso f] (n : ℕ) :
    IsIso (modulePowMap f n) := by
  induction n with
  | zero => change IsIso (𝟙 (structureSheaf X)); infer_instance
  | succ n hn => change IsIso (moduleTensorMap f (modulePowMap f n)); infer_instance

def modulePowFunctor (n : ℕ) : X.Modules ⥤ X.Modules where
  obj M := modulePow X M n
  map f := modulePowMap f n
  map_id := fun _ => modulePowMap_id _ n
  map_comp := fun _ _ => modulePowMap_comp _ _ n

def unitPowerIso : ∀ n, modulePow X (structureSheaf X) n ≅ structureSheaf X
  | 0 => Iso.refl _
  | n + 1 => moduleTensorUnit _ ≪≫ unitPowerIso n

def powerSection {M : X.Modules} (s : structureSheaf X ⟶ M) (n : ℕ) :
    structureSheaf X ⟶ modulePow X M n :=
  (unitPowerIso n).inv ≫ modulePowMap s n

instance powerSection_isIso {M : X.Modules} (s : structureSheaf X ⟶ M) [IsIso s] (n : ℕ) :
    IsIso (powerSection s n) := by unfold powerSection; infer_instance

end
end MaximalSeshadri.Geometry
namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry
variable {X : Scheme}

private lemma tensorComparison_natural
    {Source Target : Type*} [Category Source] [Category Target]
    [MonoidalCategory Source] [MonoidalCategory Target]
    (pushforward : Source ⥤ Target) [pushforward.OplaxMonoidal]
    (restriction : Source ⥤ Target) (comparison : restriction ≅ pushforward)
    {first second third fourth : Source}
    (leftMap : first ⟶ second) (rightMap : third ⟶ fourth) :
    restriction.map (leftMap ⊗ₘ rightMap) ≫
        (comparison.hom.app (second ⊗ fourth) ≫
          Functor.OplaxMonoidal.δ pushforward second fourth ≫
          (comparison.inv.app second ⊗ₘ comparison.inv.app fourth)) =
      (comparison.hom.app (first ⊗ third) ≫
        Functor.OplaxMonoidal.δ pushforward first third ≫
        (comparison.inv.app first ⊗ₘ comparison.inv.app third)) ≫
          (restriction.map leftMap ⊗ₘ restriction.map rightMap) := by
  rw [← Category.assoc, comparison.hom.naturality, Category.assoc,
    ← Category.assoc (pushforward.map (leftMap ⊗ₘ rightMap)),
    ← Functor.OplaxMonoidal.δ_natural, Category.assoc,
    tensorHom_comp_tensorHom, comparison.inv.naturality,
    comparison.inv.naturality, ← tensorHom_comp_tensorHom]
  simp only [Category.assoc]

lemma modulePresheafTensorRestrict_natural (U : X.Opens)
    {M N P Q : PresheafOfModules X.ringCatSheaf.obj}
    (f : M ⟶ N) (g : P ⟶ Q) :
    (modulePresheafRestrict U.ι).map
        (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) f g) ≫
      (modulePresheafTensorRestrict U N Q).hom =
    (modulePresheafTensorRestrict U M P).hom ≫
      PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := U.toScheme.presheaf)
        ((modulePresheafRestrict U.ι).map f) ((modulePresheafRestrict U.ι).map g) := by
  exact tensorComparison_natural
    (PresheafOfModules.pushforward₀OfCommRingCat U.ι.opensFunctor X.presheaf)
    (modulePresheafRestrict U.ι) (modulePresheafRestrictOpensIso U) f g

private lemma sheafificationComparison_natural
    {Source SourceSheaves Target TargetSheaves : Type*}
    [Category Source] [Category SourceSheaves] [Category Target] [Category TargetSheaves]
    (sourceSheafification : Source ⥤ SourceSheaves)
    (restriction : SourceSheaves ⥤ TargetSheaves)
    (presheafRestriction : Source ⥤ Target) (sheafification : Target ⥤ TargetSheaves)
    (comparison : sourceSheafification ⋙ restriction ≅ presheafRestriction ⋙ sheafification)
    {first second : Source} {restrictedFirst restrictedSecond : Target}
    (sourceMap : first ⟶ second) (targetMap : restrictedFirst ⟶ restrictedSecond)
    (firstComparison : presheafRestriction.obj first ≅ restrictedFirst)
    (secondComparison : presheafRestriction.obj second ≅ restrictedSecond)
    (naturality : presheafRestriction.map sourceMap ≫ secondComparison.hom =
      firstComparison.hom ≫ targetMap) :
    restriction.map (sourceSheafification.map sourceMap) ≫
        (comparison.app second ≪≫ sheafification.mapIso secondComparison).hom =
      (comparison.app first ≪≫ sheafification.mapIso firstComparison).hom ≫
        sheafification.map targetMap := by
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  change (sourceSheafification ⋙ restriction).map sourceMap ≫ _ = _
  rw [← Category.assoc, comparison.hom.naturality, Functor.comp_map, Category.assoc,
    ← sheafification.map_comp, naturality, sheafification.map_comp, Category.assoc]

lemma moduleTensorRestrict_natural (U : X.Opens) {M N P Q : X.Modules}
    (f : M ⟶ N) (g : P ⟶ Q) :
    (Scheme.Modules.restrictFunctor U.ι).map (moduleTensorMap f g) ≫
      (moduleTensorRestrict U N Q).hom =
    (moduleTensorRestrict U M P).hom ≫
      moduleTensorMap ((Scheme.Modules.restrictFunctor U.ι).map f)
        ((Scheme.Modules.restrictFunctor U.ι).map g) := by
  exact sheafificationComparison_natural
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
    (Scheme.Modules.restrictFunctor U.ι) (modulePresheafRestrict U.ι)
    (PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj))
    (moduleSheafificationRestrict U.ι)
    (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) f.val g.val)
    (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := U.toScheme.presheaf)
      ((modulePresheafRestrict U.ι).map f.val) ((modulePresheafRestrict U.ι).map g.val))
    (modulePresheafTensorRestrict U M.val P.val)
    (modulePresheafTensorRestrict U N.val Q.val)
    (modulePresheafTensorRestrict_natural U f.val g.val)

end
end MaximalSeshadri.Geometry
namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry
variable {X : Scheme}

lemma moduleTensorIso_hom {M N P Q : X.Modules} (e : M ≅ N) (f : P ≅ Q) :
    (moduleTensorIso e f).hom = moduleTensorMap e.hom f.hom := rfl

def modulePowRestrict (U : X.Opens) (M : X.Modules) :
    ∀ n, (modulePow X M n).restrict U.ι ≅ modulePow U.toScheme (M.restrict U.ι) n
  | 0 => Scheme.Modules.restrictUnitIso U.ι
  | n + 1 => moduleTensorRestrict U M (modulePow X M n) ≪≫
      moduleTensorIso (Iso.refl _) (modulePowRestrict U M n)

lemma modulePowRestrict_natural (U : X.Opens) {M N : X.Modules} (f : M ⟶ N) (n : ℕ) :
    (Scheme.Modules.restrictFunctor U.ι).map (modulePowMap f n) ≫
      (modulePowRestrict U N n).hom =
    (modulePowRestrict U M n).hom ≫
      modulePowMap ((Scheme.Modules.restrictFunctor U.ι).map f) n := by
  induction n with
  | zero =>
    change (Scheme.Modules.restrictFunctor U.ι).map (𝟙 (structureSheaf X)) ≫
      (Scheme.Modules.restrictUnitIso U.ι).hom =
      (Scheme.Modules.restrictUnitIso U.ι).hom ≫ 𝟙 (structureSheaf U.toScheme)
    rw [(Scheme.Modules.restrictFunctor U.ι).map_id]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  | succ n hn =>
    change (Scheme.Modules.restrictFunctor U.ι).map (moduleTensorMap f (modulePowMap f n)) ≫
      ((moduleTensorRestrict U N (modulePow X N n)).hom ≫
        (moduleTensorIso (Iso.refl _) (modulePowRestrict U N n)).hom) =
      ((moduleTensorRestrict U M (modulePow X M n)).hom ≫
        (moduleTensorIso (Iso.refl _) (modulePowRestrict U M n)).hom) ≫
          moduleTensorMap ((Scheme.Modules.restrictFunctor U.ι).map f)
            (modulePowMap ((Scheme.Modules.restrictFunctor U.ι).map f) n)
    simp only [moduleTensorIso_hom, Iso.refl_hom]
    rw [← Category.assoc, moduleTensorRestrict_natural, Category.assoc,
      ← moduleTensorMap_comp, Category.comp_id, hn]
    rw [Category.assoc, ← moduleTensorMap_comp, Category.id_comp]

lemma modulePowMap_restrict_isIso (U : X.Opens) {M N : X.Modules} (f : M ⟶ N)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map f)] (n : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (modulePowMap f n)) := by
  have h := modulePowRestrict_natural U f n
  have heq : (Scheme.Modules.restrictFunctor U.ι).map (modulePowMap f n) =
      (modulePowRestrict U M n).hom ≫
        modulePowMap ((Scheme.Modules.restrictFunctor U.ι).map f) n ≫
          (modulePowRestrict U N n).inv := by
    rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [heq]
  infer_instance

lemma powerSection_restrict_isIso (U : X.Opens) {M : X.Modules}
    (s : structureSheaf X ⟶ M)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map s)] (n : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (powerSection s n)) := by
  let := modulePowMap_restrict_isIso U s n
  unfold powerSection
  rw [(Scheme.Modules.restrictFunctor U.ι).map_comp]
  infer_instance

lemma sectionOpen_le_powerSection {M : X.Modules} (s : structureSheaf X ⟶ M) (n : ℕ) :
    sectionOpen X s ≤ sectionOpen X (powerSection s n) := by
  refine iSup_le fun U => iSup_le fun hU => ?_
  let := hU
  exact le_iSup_of_le U (le_iSup_of_le (powerSection_restrict_isIso U s n) le_rfl)

end
end MaximalSeshadri.Geometry

end
end
end

end OAI
end


