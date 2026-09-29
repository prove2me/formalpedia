-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.isIso_projectionMorphism_of_iso_free
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/f507c0fe-e3fb-51c3-b299-888640d5f148

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_ModulesProjectionMorphism
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_projectionMorphism_naturality
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_projectionMorphism_of_iso_free

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_projectionMorphism_of_iso_free.AlgebraicGeometry"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme Scheme.Modules Scheme.Modules.projectionMorphism"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.pushforward Modules.pullback Modules Modules.projectionMorphism"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "hom_ext pushforward pullback pullbackPushforwardAdjunction projectionMorphismMate projectionMorphism projectionMorphism_def projectionMorphismMate_def projectionMorphism_naturality"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace PFFree

variable {Z X : Scheme.{u}} (i : Z ⟶ X)

lemma isIso_of_iso {F F' : X.Modules} (e : F ≅ F') (h : IsIso (projectionMorphism i F')) :
    IsIso (projectionMorphism i F) := by
  have hn := projectionMorphism_naturality i e.hom
  have h1 : IsIso ((Modules.pushforward i).map ((Modules.pullback i).map e.hom)) :=
    Functor.map_isIso _ _
  have h2 : IsIso ((Modules.pushforward i).obj (𝟙_ Z.Modules) ◁ e.hom) :=
    Iso.isIso_hom (MonoidalCategory.whiskerLeftIso ((Modules.pushforward i).obj (𝟙_ Z.Modules)) e)
  have h3 : projectionMorphism i F =
      (((Modules.pushforward i).obj (𝟙_ Z.Modules) ◁ e.hom) ≫ projectionMorphism i F') ≫
        inv ((Modules.pushforward i).map ((Modules.pullback i).map e.hom)) :=
    (IsIso.eq_comp_inv _).mpr hn
  have h4 : IsIso (((Modules.pushforward i).obj (𝟙_ Z.Modules) ◁ e.hom) ≫ projectionMorphism i F') :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ h2 h
  have h5 : IsIso (inv ((Modules.pushforward i).map ((Modules.pullback i).map e.hom))) := IsIso.inv_isIso
  rw [h3]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h4 h5

lemma mate_unit :
    projectionMorphismMate i (𝟙_ X.Modules) =
      (Modules.pullback i).map ((ρ_ ((Modules.pushforward i).obj (𝟙_ Z.Modules))).hom ≫
          (Modules.pushforward i).map (Functor.Monoidal.εIso (Modules.pullback i)).hom) ≫
        (pullbackPushforwardAdjunction i).counit.app ((Modules.pullback i).obj (𝟙_ X.Modules)) := by

  let L := Modules.pullback i
  let R := Modules.pushforward i
  let adj := pullbackPushforwardAdjunction i
  let A : X.Modules := R.obj (𝟙_ Z.Modules)
  let U : Z.Modules := L.obj (𝟙_ X.Modules)
  let c : L.obj A ⟶ 𝟙_ Z.Modules := adj.counit.app (𝟙_ Z.Modules)
  let η : U ⟶ 𝟙_ Z.Modules := Functor.OplaxMonoidal.η L
  let εh : 𝟙_ Z.Modules ⟶ U := (Functor.Monoidal.εIso L).hom
  let δ : L.obj (A ⊗ 𝟙_ X.Modules) ⟶ L.obj A ⊗ U := Functor.OplaxMonoidal.δ L A (𝟙_ X.Modules)

  have f1 : projectionMorphismMate i (𝟙_ X.Modules) = δ ≫ (c ▷ U) ≫ (λ_ U).hom := by
    have := projectionMorphismMate_def i (𝟙_ X.Modules)
    rw [Functor.Monoidal.μIso_inv] at this
    exact this
  have f2 : η ≫ εh = 𝟙 U := by
    have : (Functor.Monoidal.εIso L).inv ≫ (Functor.Monoidal.εIso L).hom = 𝟙 U := (Functor.Monoidal.εIso L).inv_hom_id
    rw [Functor.Monoidal.εIso_inv] at this
    exact this
  have f3 : (𝟙_ Z.Modules ◁ η) ≫ (λ_ (𝟙_ Z.Modules)).hom = (λ_ U).hom ≫ η := leftUnitor_naturality η
  have f4 : (λ_ (𝟙_ Z.Modules)).hom = (ρ_ (𝟙_ Z.Modules)).hom := unitors_equal
  have f5 : L.map (ρ_ A).hom = δ ≫ (L.obj A ◁ η) ≫ (ρ_ (L.obj A)).hom := Functor.Monoidal.map_rightUnitor L A
  have f6 : (c ▷ 𝟙_ Z.Modules) ≫ (ρ_ (𝟙_ Z.Modules)).hom = (ρ_ (L.obj A)).hom ≫ c := rightUnitor_naturality c
  have f7 : (L.obj A ◁ η) ≫ (c ▷ 𝟙_ Z.Modules) = (c ▷ U) ≫ (𝟙_ Z.Modules ◁ η) := whisker_exchange c η
  have f8 : L.map (R.map εh) ≫ adj.counit.app U = c ≫ εh := adj.counit.naturality εh

  have g1 : (λ_ U).hom = (𝟙_ Z.Modules ◁ η) ≫ (ρ_ (𝟙_ Z.Modules)).hom ≫ εh := by
    calc (λ_ U).hom = (λ_ U).hom ≫ (η ≫ εh) := by rw [f2, Category.comp_id]
      _ = ((λ_ U).hom ≫ η) ≫ εh := (Category.assoc _ _ _).symm
      _ = ((𝟙_ Z.Modules ◁ η) ≫ (λ_ (𝟙_ Z.Modules)).hom) ≫ εh := by rw [f3]
      _ = (𝟙_ Z.Modules ◁ η) ≫ (ρ_ (𝟙_ Z.Modules)).hom ≫ εh := by rw [f4, Category.assoc]

  have f6' : (ρ_ (L.obj A)).hom ≫ c ≫ εh = (c ▷ 𝟙_ Z.Modules) ≫ (ρ_ (𝟙_ Z.Modules)).hom ≫ εh := by
    rw [← Category.assoc, ← f6, Category.assoc]
  have f7' : (L.obj A ◁ η) ≫ (c ▷ 𝟙_ Z.Modules) ≫ (ρ_ (𝟙_ Z.Modules)).hom ≫ εh =
      (c ▷ U) ≫ (𝟙_ Z.Modules ◁ η) ≫ (ρ_ (𝟙_ Z.Modules)).hom ≫ εh := by
    rw [← Category.assoc, f7, Category.assoc]
  have g2 : L.map ((ρ_ A).hom ≫ R.map εh) ≫ adj.counit.app U =
      δ ≫ (c ▷ U) ≫ (𝟙_ Z.Modules ◁ η) ≫ (ρ_ (𝟙_ Z.Modules)).hom ≫ εh := by
    have s1 : L.map ((ρ_ A).hom ≫ R.map εh) ≫ adj.counit.app U =
        L.map (ρ_ A).hom ≫ (L.map (R.map εh) ≫ adj.counit.app U) :=
      (congrArg (· ≫ adj.counit.app U) (L.map_comp _ _)).trans (Category.assoc _ _ _)
    have s2 : L.map (ρ_ A).hom ≫ (L.map (R.map εh) ≫ adj.counit.app U) =
        (δ ≫ (L.obj A ◁ η) ≫ (ρ_ (L.obj A)).hom) ≫ (c ≫ εh) :=
      (congrArg (L.map (ρ_ A).hom ≫ ·) f8).trans (congrArg (· ≫ (c ≫ εh)) f5)
    have s3 : (δ ≫ (L.obj A ◁ η) ≫ (ρ_ (L.obj A)).hom) ≫ (c ≫ εh) =
        δ ≫ (L.obj A ◁ η) ≫ ((ρ_ (L.obj A)).hom ≫ c ≫ εh) :=
      (Category.assoc _ _ _).trans (congrArg (δ ≫ ·) (Category.assoc _ _ _))
    have s4 : δ ≫ (L.obj A ◁ η) ≫ ((ρ_ (L.obj A)).hom ≫ c ≫ εh) =
        δ ≫ (c ▷ U) ≫ (𝟙_ Z.Modules ◁ η) ≫ (ρ_ (𝟙_ Z.Modules)).hom ≫ εh :=
      congrArg (δ ≫ ·) ((congrArg ((L.obj A ◁ η) ≫ ·) f6').trans f7')
    exact s1.trans (s2.trans (s3.trans s4))
  change projectionMorphismMate i (𝟙_ X.Modules) = L.map ((ρ_ A).hom ≫ R.map εh) ≫ adj.counit.app U
  exact f1.trans ((congrArg (fun t => δ ≫ (c ▷ U) ≫ t) g1).trans g2.symm)

lemma projectionMorphism_unit :
    projectionMorphism i (𝟙_ X.Modules) =
      (ρ_ ((Modules.pushforward i).obj (𝟙_ Z.Modules))).hom ≫
        (Modules.pushforward i).map (Functor.Monoidal.εIso (Modules.pullback i)).hom := by
  rw [projectionMorphism_def, mate_unit, Equiv.apply_eq_iff_eq_symm_apply]
  exact ((pullbackPushforwardAdjunction i).homEquiv_counit _ _ _).symm

lemma isIso_unit : IsIso (projectionMorphism i (𝟙_ X.Modules)) := by
  rw [projectionMorphism_unit]
  have h1 : IsIso (ρ_ ((Modules.pushforward i).obj (𝟙_ Z.Modules))).hom := Iso.isIso_hom _
  have h2 : IsIso ((Modules.pushforward i).map (Functor.Monoidal.εIso (Modules.pullback i)).hom) :=
    Functor.map_isIso _ _
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2

section biproduct

variable (n : ℕ)

noncomputable abbrev fam (X : Scheme.{u}) (n : ℕ) : Fin n → X.Modules := fun _ => 𝟙_ X.Modules

lemma isIso_biproduct [HasFiniteBiproducts X.Modules] :
    IsIso (projectionMorphism i (⨁ fam X n)) := by
  let L := Modules.pullback i
  let R := Modules.pushforward i
  let A : X.Modules := R.obj (𝟙_ Z.Modules)
  let G₁ : X.Modules ⥤ X.Modules := tensorLeft A
  let G₂ : X.Modules ⥤ X.Modules := L ⋙ R
  haveI : PreservesBinaryBiproducts G₁ := preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  haveI : G₁.Additive := Functor.additive_of_preservesBinaryBiproducts G₁
  let θ : ∀ F : X.Modules, G₁.obj F ⟶ G₂.obj F := fun F => projectionMorphism i F
  have hθ : ∀ {F F' : X.Modules} (φ : F ⟶ F'), θ F ≫ G₂.map φ = G₁.map φ ≫ θ F' :=
    fun φ => projectionMorphism_naturality i φ
  let m₁ : G₁.obj (⨁ fam X n) ≅ ⨁ (G₁.obj ∘ fam X n) := G₁.mapBiproduct (fam X n)
  let m₂ : G₂.obj (⨁ fam X n) ≅ ⨁ (G₂.obj ∘ fam X n) := G₂.mapBiproduct (fam X n)
  let bm : (⨁ (G₁.obj ∘ fam X n)) ⟶ ⨁ (G₂.obj ∘ fam X n) := biproduct.map (fun j => θ (fam X n j))
  have key : θ (⨁ fam X n) ≫ m₂.hom = m₁.hom ≫ bm := by
    apply biproduct.hom_ext
    intro j
    have e1 : m₂.hom ≫ biproduct.π (G₂.obj ∘ fam X n) j = G₂.map (biproduct.π (fam X n) j) := by
      change (G₂.mapBiproduct (fam X n)).hom ≫ _ = _
      rw [Functor.mapBiproduct_hom]
      exact biproduct.lift_π _ _
    have e2 : m₁.hom ≫ biproduct.π (G₁.obj ∘ fam X n) j = G₁.map (biproduct.π (fam X n) j) := by
      change (G₁.mapBiproduct (fam X n)).hom ≫ _ = _
      rw [Functor.mapBiproduct_hom]
      exact biproduct.lift_π _ _
    have e3 : bm ≫ biproduct.π (G₂.obj ∘ fam X n) j = biproduct.π (G₁.obj ∘ fam X n) j ≫ θ (fam X n j) :=
      biproduct.map_π _ j
    have Lj : (θ (⨁ fam X n) ≫ m₂.hom) ≫ biproduct.π (G₂.obj ∘ fam X n) j =
        G₁.map (biproduct.π (fam X n) j) ≫ θ (fam X n j) :=
      (Category.assoc _ _ _).trans ((congrArg (θ (⨁ fam X n) ≫ ·) e1).trans (hθ (biproduct.π (fam X n) j)))
    have Rj : (m₁.hom ≫ bm) ≫ biproduct.π (G₂.obj ∘ fam X n) j =
        G₁.map (biproduct.π (fam X n) j) ≫ θ (fam X n j) :=
      (Category.assoc _ _ _).trans ((congrArg (m₁.hom ≫ ·) e3).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ θ (fam X n j)) e2)))
    exact Lj.trans Rj.symm
  have hbm : IsIso bm := by
    have : bm = (biproduct.mapIso (fun j => @asIso _ _ _ _ (θ (fam X n j)) (isIso_unit i))).hom := by
      rw [biproduct.mapIso_hom]
      rfl
    rw [this]
    exact Iso.isIso_hom _
  have hθeq : θ (⨁ fam X n) = (m₁.hom ≫ bm) ≫ m₂.inv := (Iso.eq_comp_inv m₂).mpr key
  have h2 : IsIso (m₁.hom ≫ bm) := @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_hom _) hbm
  change IsIso (θ (⨁ fam X n))
  rw [hθeq]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h2 (Iso.isIso_inv _)

end biproduct

theorem main {n : ℕ} (F : X.Modules) (e : F ≅ SheafOfModules.free.{u} (ULift.{u} (Fin n))) :
    IsIso (projectionMorphism i F) := by
  haveI : HasFiniteBiproducts X.Modules := Abelian.hasFiniteBiproducts

  let e₁ : (SheafOfModules.free.{u} (ULift.{u} (Fin n)) : X.Modules) ≅ ∐ fam X n :=
    Limits.Sigma.reindex (Equiv.ulift : ULift.{u} (Fin n) ≃ Fin n) (fam X n)
  let e₂ : (∐ fam X n) ≅ ⨁ fam X n := (biproduct.isoCoproduct (fam X n)).symm
  exact isIso_of_iso i ((e ≪≫ e₁) ≪≫ e₂) (isIso_biproduct i n)

end PFFree

end AlgebraicGeometry.Scheme.Modules

theorem solution
    {Z X : Scheme.{u}} (i : Z ⟶ X) {n : ℕ} (F : X.Modules)
    (e : F ≅ SheafOfModules.free.{u} (ULift.{u} (Fin n))) :
    IsIso (Scheme.Modules.projectionMorphism i F) :=
  AlgebraicGeometry.Scheme.Modules.PFFree.main i F e

end S_AlgebraicGeometry_Scheme_Modules_isIso_projectionMorphism_of_iso_free
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_projectionMorphism_of_iso_free (solution)
