-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.etaleFrame_tensor_restrict
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-19T14:55:48.066717+00:00
-- url     : https://prove2.me/submissions/e37c2089-ca5c-417e-b294-e3d8f2e0070e

import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import Mathlib.CategoryTheory.EssentialImage
import Definitions.Def_PresheafOfModules_PullbackMonoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PresheafPullbackCompositionComparison
import Definitions.Def_AlgebraicGeometry_EtaleFramePresentations

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 256

open CategoryTheory MonoidalCategory

namespace PhilipponMonoidalAdjunctionMates

private theorem monoidal_comp {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] {F G H : C ⥤ D}
    [F.LaxMonoidal] [G.LaxMonoidal] [H.LaxMonoidal]
    (α : F ⟶ G) (β : G ⟶ H) (hα : α.IsMonoidal) (hβ : β.IsMonoidal) :
    (α ≫ β).IsMonoidal :=
  NatTrans.IsMonoidal.comp α β

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
  (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
  [L₁.Monoidal] [L₂.Monoidal] [R₁.LaxMonoidal] [R₂.LaxMonoidal]
  [a₁.IsMonoidal] [a₂.IsMonoidal]

/-- Mates between the right adjoints of monoidal adjunctions preserve the
unit and tensor constraints. -/
theorem rightMate (α : L₂ ⟶ L₁) [α.IsMonoidal] :
    (conjugateEquiv a₁ a₂ α).IsMonoidal := by
  let κ : (R₁ ⋙ L₁) ⋙ R₂ ⟶ (𝟭 D) ⋙ R₂ := a₁.counit ◫ 𝟙 R₂
  have hκ : κ.IsMonoidal := by
    dsimp only [κ]
    infer_instance
  have h : conjugateEquiv a₁ a₂ α =
      R₁.rightUnitor.inv ≫ (𝟙 R₁ ◫ a₂.unit) ≫
        (Functor.associator R₁ L₂ R₂).inv ≫ ((𝟙 R₁ ◫ α) ◫ 𝟙 R₂) ≫
        κ ≫ R₂.leftUnitor.hom := by
    ext X
    simp [κ]
  rw [h]
  repeat' apply monoidal_comp
  all_goals first | exact hκ | infer_instance

/-- Mates between the left adjoints likewise preserve both constraints. -/
theorem leftMate (β : R₁ ⟶ R₂) [β.IsMonoidal] :
    ((conjugateEquiv a₁ a₂).symm β).IsMonoidal := by
  have h : (conjugateEquiv a₁ a₂).symm β =
      L₂.leftUnitor.inv ≫ (a₁.unit ◫ 𝟙 L₂) ≫
        (Functor.associator L₁ R₁ L₂).hom ≫ (𝟙 L₁ ◫ (β ◫ 𝟙 L₂)) ≫
        (𝟙 L₁ ◫ a₂.counit) ≫ L₁.rightUnitor.hom := by
    ext X
    simp
  rw [h]
  infer_instance

end PhilipponMonoidalAdjunctionMates
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open CategoryTheory MonoidalCategory
open Functor.LaxMonoidal Functor.Monoidal

namespace PhilipponMonoidalTensorFrames

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]

def tensor {A B : C} (p : 𝟙_ C ≅ A) (q : 𝟙_ C ≅ B) : 𝟙_ C ≅ A ⊗ B :=
  (λ_ (𝟙_ C)).symm ≪≫ (p ⊗ᵢ q)

theorem tensor_postcompose {A B A' B' : C} (p : 𝟙_ C ≅ A) (q : 𝟙_ C ≅ B)
    (a : A ≅ A') (b : B ≅ B') :
    tensor (p ≪≫ a) (q ≪≫ b) = tensor p q ≪≫ (a ⊗ᵢ b) := by
  apply Iso.ext
  simp only [tensor, Iso.trans_hom, tensorIso_hom, Category.assoc,
    tensorHom_comp_tensorHom]

variable (F : C ⥤ D) [F.Monoidal]

def pull {A : C} (p : 𝟙_ C ≅ A) : 𝟙_ D ≅ F.obj A :=
  εIso F ≪≫ F.mapIso p

theorem pull_postcompose {A B : C} (p : 𝟙_ C ≅ A) (e : A ≅ B) :
    pull F (p ≪≫ e) = pull F p ≪≫ F.mapIso e := by
  apply Iso.ext
  simp only [pull, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]

private theorem unit_tensor :
    (ε F) ≫ F.map (λ_ (𝟙_ C)).inv =
      (λ_ (𝟙_ D)).inv ≫ ((ε F) ⊗ₘ (ε F)) ≫ μ F (𝟙_ C) (𝟙_ C) := by
  apply (cancel_mono (F.map (λ_ (𝟙_ C)).hom)).mp
  simp only [Category.assoc, ← F.map_comp, Iso.inv_hom_id, F.map_id, Category.comp_id]
  rw [tensorHom_def'_assoc, ← left_unitality F, leftUnitor_naturality, Iso.inv_hom_id_assoc]

theorem pull_tensor {A B : C} (p : 𝟙_ C ≅ A) (q : 𝟙_ C ≅ B) :
    pull F (tensor p q) = tensor (pull F p) (pull F q) ≪≫ μIso F A B := by
  apply Iso.ext
  simp only [pull, tensor, Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Functor.mapIso_hom,
    Functor.map_comp, εIso_hom, μIso_hom, Category.assoc]
  rw [reassoc_of% (unit_tensor F), ← tensorHom_comp_tensorHom, Category.assoc, μ_natural]

section Composition

variable {E : Type*} [Category* E] [MonoidalCategory E]
  (G : D ⥤ E) (H : C ⥤ E) [G.Monoidal] [H.Monoidal]

/-- Transport of tensor frames through a monoidal comparison for a composite. -/
theorem pull_comp (c : F ⋙ G ≅ H) [c.hom.IsMonoidal] {A B L : C} (e : A ⊗ B ≅ L)
    (p : 𝟙_ D ≅ F.obj A) (q : 𝟙_ D ≅ F.obj B) :
    pull G (tensor p q ≪≫ μIso F A B ≪≫ F.mapIso e) ≪≫ c.app L =
      tensor (pull G p ≪≫ c.app A) (pull G q ≪≫ c.app B) ≪≫ μIso H A B ≪≫ H.mapIso e := by
  have hn : G.mapIso (F.mapIso e) ≪≫ c.app L = c.app (A ⊗ B) ≪≫ H.mapIso e := by
    apply Iso.ext
    exact c.hom.naturality e.hom
  have hm : μIso G (F.obj A) (F.obj B) ≪≫ G.mapIso (μIso F A B) ≪≫ c.app (A ⊗ B) =
      (c.app A ⊗ᵢ c.app B) ≪≫ μIso H A B := by
    apply Iso.ext
    simp only [Iso.trans_hom, μIso_hom, Functor.mapIso_hom, tensorIso_hom]
    change μ G (F.obj A) (F.obj B) ≫ G.map (μ F A B) ≫ c.hom.app (A ⊗ B) =
      (c.hom.app A ⊗ₘ c.hom.app B) ≫ μ H A B
    simpa only [Category.assoc, comp_μ, Functor.comp_obj] using
      NatTrans.IsMonoidal.tensor (τ := c.hom) A B
  simp only [← Iso.trans_assoc, pull_postcompose, pull_tensor, tensor_postcompose]
  simp only [Iso.trans_assoc]
  rw [hn, ← Iso.trans_assoc (G.mapIso (μIso F A B)), ← Iso.trans_assoc (μIso G _ _), hm]
  simp only [Iso.trans_assoc]

end Composition

end PhilipponMonoidalTensorFrames
end
end

section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Category MonoidalCategory
open Functor.LaxMonoidal

namespace PhilipponMonoidalWhiskerReflection

variable {A C D : Type*} [Category* A] [Category* C] [Category* D]
  [MonoidalCategory A] [MonoidalCategory C] [MonoidalCategory D]
  {F G : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal] (α : F ⟶ G)

private theorem tensor_of_iso {X X' Y Y' : C} (x : X ≅ X') (y : Y ≅ Y')
    (h : μ F X Y ≫ α.app (X ⊗ Y) = (α.app X ⊗ₘ α.app Y) ≫ μ G X Y) :
    μ F X' Y' ≫ α.app (X' ⊗ Y') = (α.app X' ⊗ₘ α.app Y') ≫ μ G X' Y' := by
  apply (cancel_epi (F.map x.hom ⊗ₘ F.map y.hom)).mp
  rw [μ_natural_assoc, α.naturality, ← Category.assoc, h, Category.assoc, ← μ_natural,
    tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc, α.naturality, α.naturality]

/-- Precomposing with a strong monoidal functor surjective up to isomorphism
reflects monoidality of natural transformations. -/
theorem of_whiskerLeft (I : A ⥤ C) [I.Monoidal] [I.EssSurj]
    [(Functor.whiskerLeft I α).IsMonoidal] : α.IsMonoidal := by
  constructor
  · have h := NatTrans.IsMonoidal.unit (τ := Functor.whiskerLeft I α)
    simp only [comp_ε, Functor.whiskerLeft_app] at h
    rw [Category.assoc, α.naturality, ← Category.assoc] at h
    exact (cancel_mono (G.map (ε I))).mp h
  · intro X Y
    obtain ⟨P, ⟨x⟩⟩ := Functor.EssSurj.mem_essImage I X
    obtain ⟨Q, ⟨y⟩⟩ := Functor.EssSurj.mem_essImage I Y
    apply tensor_of_iso α x y
    have h := NatTrans.IsMonoidal.tensor (τ := Functor.whiskerLeft I α) P Q
    simp only [comp_μ, Functor.whiskerLeft_app, Functor.comp_obj] at h
    rw [Category.assoc, α.naturality, ← Category.assoc] at h
    apply (cancel_mono (G.map (μ I P Q))).mp
    simpa only [Category.assoc] using h

end PhilipponMonoidalWhiskerReflection
end

section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TensorProduct
open CategoryTheory.Functor
open Functor.LaxMonoidal
open PresheafOfModules PresheafOfModules.PullbackMonoidal

namespace PhilipponPresheafModuleMonoidalComposition
universe u

variable {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
  [HasFiniteProducts C] [HasFiniteProducts D] [HasFiniteProducts E]
  (F : C ⥤ D) (G : D ⥤ E) [PreservesFiniteProducts F] [PreservesFiniteProducts G]
  {R : Eᵒᵖ ⥤ CommRingCat.{u}} {S : Dᵒᵖ ⥤ CommRingCat.{u}} {T : Cᵒᵖ ⥤ CommRingCat.{u}}
  (φ : T ⟶ F.op ⋙ S) (ψ : S ⟶ G.op ⋙ R)

theorem epsilon_apply (U : Cᵒᵖ) (r : T.obj U) :
    ((ε (pf F φ)).app U).hom r = φ.app U r := by
  let rs := PresheafOfModules.restrictScalars (ringCatHom (R := F.op ⋙ S) φ)
  have h : ε rs ≫ rs.map (ε (pushforward₀OfCommRingCat F S)) = ε rs := by
    change ε rs ≫ rs.map (𝟙 _) = ε rs
    rw [rs.map_id, Category.comp_id]
  change ((ε rs ≫ rs.map (ε (pushforward₀OfCommRingCat F S))).app U).hom r = _
  erw [h]
  exact ModuleCat.restrictScalars_η (φ.app U).hom r

abbrev comparison :
    pf G ψ ⋙ pf F φ ≅ pf (F ⋙ G) (φ ≫ whiskerLeft F.op ψ) := by
  exact PresheafOfModules.pushforwardComp.{u} (F := F) (G := G)
    (R := S ⋙ forget₂ CommRingCat RingCat) (S := T ⋙ forget₂ CommRingCat RingCat)
    (T := R ⋙ forget₂ CommRingCat RingCat) (ringCatHom φ) (ringCatHom ψ)

private theorem epsilon_comp_apply (U : Cᵒᵖ) (r : T.obj U) :
    ((ε (pf G ψ ⋙ pf F φ)).app U).hom r = ψ.app (F.op.obj U) (φ.app U r) := by
  have hF := epsilon_apply F φ U r
  have hG := epsilon_apply G ψ (F.op.obj U) (φ.app U r)
  simp only [comp_ε, PresheafOfModules.comp_app]
  erw [ModuleCat.comp_apply, hF]
  exact hG

/-- The pointwise tensor maps of pushforward compose with the maps of rings. -/
theorem pushforwardComp_monoidal : (comparison F G φ ψ).hom.IsMonoidal := by
  constructor
  · have h : (comparison F G φ ψ).hom.app (𝟙_ _) = 𝟙 _ := rfl
    rw [h, Category.comp_id]
    ext1 U
    apply ModuleCat.hom_ext
    ext1
    have h := epsilon_comp_apply F G φ ψ U (1 : T.obj U)
    have h' := epsilon_apply (F ⋙ G) (φ ≫ whiskerLeft F.op ψ) U (1 : T.obj U)
    exact h.trans h'.symm
  · intro M N
    have hM : (comparison F G φ ψ).hom.app M = 𝟙 _ := rfl
    have hN : (comparison F G φ ψ).hom.app N = 𝟙 _ := rfl
    have hP : (comparison F G φ ψ).hom.app (M ⊗ N) = 𝟙 _ := rfl
    rw [hM, hN, hP, Category.comp_id, tensorHom_id, id_whiskerRight, Category.id_comp]
    ext1 U
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    have hF := pf_μ_app_tmul F φ ((pf G ψ).obj M) ((pf G ψ).obj N) U.unop m n
    have hFG := pf_μ_app_tmul (F ⋙ G) (φ ≫ whiskerLeft F.op ψ) M N U.unop m n
    simp only [op_unop] at hF hFG
    simp only [LaxMonoidal.comp_μ, PresheafOfModules.comp_app, Functor.comp_obj]
    erw [ModuleCat.comp_apply, hF, hFG]

end PhilipponPresheafModuleMonoidalComposition
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

namespace PhilipponSchemeMonoidalPullbackUnit
universe u

private abbrev a (X : Scheme.{u}) := SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property
private abbrev L (X : Scheme.{u}) := Scheme.Modules.sheafify X
private abbrev Q (X : Scheme.{u}) := SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property

private theorem counit_at_unit (X : Scheme.{u}) :
    η (L X) = (a X).counit.app (𝟙_ X.Modules) := rfl

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

private abbrev P := Scheme.Modules.pullback₀ f
private abbrev F := Scheme.Modules.pullback f
private abbrev b := PresheafOfModules.PullbackMonoidal.adj (Opens.map f.base) f.c
private abbrev d := Scheme.Modules.pullbackPushforwardAdjunction f
private abbrev c : L Y ⋙ F f ≅ P f ⋙ L X :=
  SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom

theorem lifting_monoidal : NatTrans.IsMonoidal (c f).hom := by
  let W := SheafOfModules.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj
  exact Localization.Monoidal.lifting_isMonoidal (L Y) W (F f) (P f ⋙ L X)

private theorem comparison_η :
    (F f).map (η (L Y)) ≫ η (F f) =
      (c f).hom.app (𝟙_ Y.PresheafOfModules) ≫ (L X).map (η (P f)) ≫ η (L X) := by
  let : NatTrans.IsMonoidal (c f).hom := lifting_monoidal f
  let i := εIso (F f) ≪≫ (F f).mapIso (εIso (L Y)) ≪≫ (c f).app (𝟙_ Y.PresheafOfModules)
  let j := εIso (L X) ≪≫ (L X).mapIso (εIso (P f))
  have h : i = j := by
    apply Iso.ext
    exact NatTrans.IsMonoidal.unit (τ := (c f).hom)
  have k := congrArg Iso.inv h
  apply (cancel_epi ((c f).inv.app (𝟙_ Y.PresheafOfModules))).mp
  simpa only [i, j, Iso.trans_inv, εIso_inv, Functor.mapIso_inv, Category.assoc,
    Iso.app_inv, Iso.inv_hom_id_app_assoc] using k

private theorem presheaf_ε :
    ε (PresheafOfModules.PullbackMonoidal.pf (Opens.map f.base) f.c) =
      (Q Y).map (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
  ext1 U
  apply ModuleCat.hom_ext
  ext1
  let rs := PresheafOfModules.restrictScalars
    (PresheafOfModules.ringCatHom (R := (Opens.map f.base).op ⋙ X.sheaf.obj) f.c)
  let fp := PresheafOfModules.pushforward₀OfCommRingCat (Opens.map f.base) X.sheaf.obj
  have h : ε rs ≫ rs.map (ε fp) = ε rs := by
    change ε rs ≫ rs.map (𝟙 _) = ε rs
    rw [rs.map_id, Category.comp_id]
  change ((ε rs ≫ rs.map (ε fp)).app U).hom (1 : Y.sheaf.obj.obj U) = f.c.app U 1
  erw [h]
  exact ModuleCat.restrictScalars_η (f.c.app U).hom 1

private theorem transpose {A B : Type*} [Category* A] [Category* B]
    {F₁ F₂ : A ⥤ B} {G : B ⥤ A} (a₁ : F₁ ⊣ G) (a₂ : F₂ ⊣ G)
    (M : A) (N : B) (k : F₂.obj M ⟶ N) :
    a₁.homEquiv M N ((a₁.leftAdjointUniq a₂).hom.app M ≫ k) =
      a₂.homEquiv M N k := by
  rw [a₁.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app,
    Adjunction.homEquiv_unit]

section ComposedAdjunction

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  {L : A ⥤ B} {Q : B ⥤ A} {F : B ⥤ C} {G : C ⥤ B}
  (a : L ⊣ Q) (d : F ⊣ G)

private theorem transpose_counit_before {U : B} {V : C} (m : F.obj U ⟶ V) :
    (a.comp d).homEquiv (Q.obj U) V (F.map (a.counit.app U) ≫ m) =
      Q.map (d.homEquiv U V m) := by
  rw [Adjunction.comp_homEquiv]
  change a.homEquiv _ _ (d.homEquiv _ _ (F.map (a.counit.app U) ≫ m)) = _
  rw [d.homEquiv_naturality_left, a.homEquiv_naturality_right]
  simp only [Functor.id_obj, ← a.homEquiv_symm_id, Equiv.apply_symm_apply, Category.id_comp]

private theorem transpose_counit_after {U : A} {V : C} (m : L.obj U ⟶ G.obj V) :
    (a.comp d).homEquiv U V (F.map m ≫ d.counit.app V) = a.homEquiv U (G.obj V) m := by
  rw [Adjunction.comp_homEquiv]
  change a.homEquiv _ _ (d.homEquiv _ _ (F.map m ≫ d.counit.app V)) = _
  simp only [Functor.id_obj, ← d.homEquiv_counit, Equiv.apply_symm_apply]

end ComposedAdjunction

/-- The unit obtained by descending the monoidal structure through
sheafification is the unit comparison used to restrict frames. -/
theorem pullbackUnitIso_eq :
    Scheme.Modules.pullbackUnitIso f = (εIso (F f)).symm := by
  apply Iso.ext
  change (Scheme.Modules.pullbackUnitIso f).hom = η (F f)
  apply (cancel_epi ((F f).map (η (L Y)))).mp
  rw [comparison_η f]
  let a₁ := (a Y).comp (d f)
  let a₂ := (b f).comp (a X)
  apply (a₁.homEquiv (𝟙_ Y.PresheafOfModules) (𝟙_ X.Modules)).injective
  let u := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  have h₁ : (d f).homEquiv _ _ (Scheme.Modules.pullbackUnitIso f).hom = u :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  have h₂ : (c f).hom = (Adjunction.leftAdjointUniq a₁ a₂).hom := rfl
  rw [h₂, transpose a₁ a₂]
  have hleft : a₁.homEquiv (𝟙_ Y.PresheafOfModules) (𝟙_ X.Modules)
      ((F f).map (η (L Y)) ≫ (Scheme.Modules.pullbackUnitIso f).hom) = (Q Y).map u := by
    rw [counit_at_unit, ← h₁]
    with_unfolding_all
      exact transpose_counit_before (a Y) (d f) (Scheme.Modules.pullbackUnitIso f).hom
  have hright : a₂.homEquiv (𝟙_ Y.PresheafOfModules) (𝟙_ X.Modules)
      ((L X).map (η (P f)) ≫ η (L X)) =
        ε (PresheafOfModules.PullbackMonoidal.pf (Opens.map f.base) f.c) := by
    rw [counit_at_unit]
    change ((b f).comp (a X)).homEquiv _ _ _ = _
    rw [transpose_counit_after]
    exact Equiv.apply_symm_apply _ _
  exact hleft.trans ((presheaf_ε f).symm.trans hright.symm)

end PhilipponSchemeMonoidalPullbackUnit
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PhilipponAdjointCompositionComparisons

namespace PhilipponSchemePullbackSheafificationComposition
universe u

private abbrev a (X : Scheme.{u}) :=
  SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Monoidality of the presheaf comparison descends along sheafification. -/
theorem monoidal_of_presheaf (h : (presheafComp f g).hom.IsMonoidal) :
    (Scheme.Modules.pullbackComp f g).hom.IsMonoidal := by
  let : (lifted f).hom.IsMonoidal := PhilipponSchemeMonoidalPullbackUnit.lifting_monoidal f
  let : (lifted g).hom.IsMonoidal := PhilipponSchemeMonoidalPullbackUnit.lifting_monoidal g
  let : (lifted (f ≫ g)).hom.IsMonoidal :=
    PhilipponSchemeMonoidalPullbackUnit.lifting_monoidal (f ≫ g)
  let t := Functor.whiskerLeft (L Z) (Scheme.Modules.pullbackComp f g).hom
  let : (t ≫ (lifted (f ≫ g)).hom).IsMonoidal := by
    dsimp only [t]
    rw [commuting_comparisons f g]
    infer_instance
  let : t.IsMonoidal := by
    have hm := NatTrans.IsMonoidal.comp (t ≫ (lifted (f ≫ g)).hom) (lifted (f ≫ g)).inv
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hm
  let : (L Z).EssSurj := ⟨fun M => ⟨(SheafOfModules.toPMod Z.sheaf.obj
    Z.ringCatSheaf.property).obj M, ⟨(asIso (a Z).counit).app M⟩⟩⟩
  exact PhilipponMonoidalWhiskerReflection.of_whiskerLeft _ (L Z)

end PhilipponSchemePullbackSheafificationComposition
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory
open Functor.Monoidal
open PhilipponEtaleFrameSections PhilipponTensorFrames

namespace PhilipponEtaleTensorRestriction
universe u

private theorem monoidal_pullbackCongr {X Y : Scheme.{u}} {f g : Y ⟶ X} (h : f = g) :
    (Scheme.Modules.pullbackCongr h).hom.IsMonoidal := by
  subst g
  change NatTrans.IsMonoidal (𝟙 (Scheme.Modules.pullback f))
  infer_instance

/-- The condition on the two pullback comparisons needed by tensoring
étale frames. The congruence along an equality of scheme maps is automatic. -/
theorem of_monoidal_comparisons {X : Scheme.{u}} {M N L : X.Modules}
    (e : M ⊗ N ≅ L) {U V : X.Etale} (f : V ⟶ U) (p : Frame M U) (q : Frame N U)
    (hunit : Scheme.Modules.pullbackUnitIso f.left =
      (εIso (Scheme.Modules.pullback f.left)).symm)
    (hcomp : (Scheme.Modules.pullbackComp f.left U.hom).hom.IsMonoidal) :
    restrict L f (tensorOn e U p q) = tensorOn e V (restrict M f p) (restrict N f q) := by
  let c := Scheme.Modules.pullbackComp f.left U.hom ≪≫
    Scheme.Modules.pullbackCongr (MorphismProperty.Over.w f)
  let : NatTrans.IsMonoidal (Scheme.Modules.pullbackCongr (MorphismProperty.Over.w f)).hom :=
    monoidal_pullbackCongr _
  let : c.hom.IsMonoidal := by
    dsimp only [c, Iso.trans_hom]
    infer_instance
  have h := PhilipponMonoidalTensorFrames.pull_comp (Scheme.Modules.pullback U.hom)
    (Scheme.Modules.pullback f.left) (Scheme.Modules.pullback V.hom) c e p q
  simpa only [Frame, Functor.id_obj, restrict, PhilipponFramePullback.pullFrame, PhilipponFramePullback.unitIso, hunit,
    Iso.symm_symm_eq, tensorOn, tensorFrame, PhilipponMonoidalTensorFrames.pull,
    PhilipponMonoidalTensorFrames.tensor, c, NatIso.trans_app, Iso.trans_assoc] using h

end PhilipponEtaleTensorRestriction
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace MonoidalCategory
open PhilipponEtaleFrameSections PhilipponTensorFrames
open PhilipponSchemePullbackSheafificationComposition

namespace PhilipponEtaleTensorRestrictionProof
universe u
variable {X Y Z : Scheme.{u}}

private theorem presheaf_adj_monoidal (f : X ⟶ Y) : (b f).IsMonoidal := by
  exact inferInstanceAs (letI := (b f).leftAdjointOplaxMonoidal; (b f).IsMonoidal)

private theorem presheafComp_monoidal (f : X ⟶ Y) (g : Y ⟶ Z) :
    (presheafComp f g).hom.IsMonoidal := by
  let : (b f).IsMonoidal := presheaf_adj_monoidal f
  let : (b g).IsMonoidal := presheaf_adj_monoidal g
  let : (b (f ≫ g)).IsMonoidal := presheaf_adj_monoidal (f ≫ g)
  let c := PhilipponPresheafModuleMonoidalComposition.comparison
    (Opens.map g.base) (Opens.map f.base) g.c f.c
  let : c.hom.IsMonoidal := PhilipponPresheafModuleMonoidalComposition.pushforwardComp_monoidal
    (Opens.map g.base) (Opens.map f.base) g.c f.c
  have h := PhilipponMonoidalAdjunctionMates.leftMate (b (f ≫ g)) ((b g).comp (b f)) c.inv
  change (Adjunction.leftAdjointCompIso (b g) (b f) (b (f ≫ g)) c).hom.IsMonoidal at h
  have e : (Adjunction.leftAdjointCompIso (b g) (b f) (b (f ≫ g)) c).hom =
      (presheafComp f g).hom :=
    PhilipponAdjointCompositionComparisons.leftAdjointCompIso_hom_of_identity
      (b g) (b f) (b (f ≫ g))
  exact e ▸ h

/-- Tensoring frames commutes with restriction on the small étale site. -/
theorem tensor_restrict {M N L : X.Modules} (e : M ⊗ N ≅ L)
    {U V : X.Etale} (f : V ⟶ U) (p : Frame M U) (q : Frame N U) :
    restrict L f (tensorOn e U p q) = tensorOn e V (restrict M f p) (restrict N f q) :=
  PhilipponEtaleTensorRestriction.of_monoidal_comparisons e f p q
    (PhilipponSchemeMonoidalPullbackUnit.pullbackUnitIso_eq f.left)
    (monoidal_of_presheaf f.left U.hom (presheafComp_monoidal f.left U.hom))

end PhilipponEtaleTensorRestrictionProof
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory MonoidalCategory
open PhilipponTorsorSectionFibers PhilipponEtaleFrameTorsor PhilipponEtaleFrameSections
open PhilipponTensorFrames
universe u

theorem solution {X : Scheme.{u}} {M N L : X.Modules} (e : M ⊗ N ≅ L)
    {U V : X.Etale} (f : V ⟶ U) (p : Frame M U) (q : Frame N U) :
    PhilipponEtaleFrameSections.restrict L f (tensorOn e U p q) =
      tensorOn e V (PhilipponEtaleFrameSections.restrict M f p)
        (PhilipponEtaleFrameSections.restrict N f q) := by
  exact PhilipponEtaleTensorRestrictionProof.tensor_restrict e f p q

#print axioms solution
