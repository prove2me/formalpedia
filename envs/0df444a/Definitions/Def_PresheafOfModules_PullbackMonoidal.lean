-- Prove2me | Definitions.Def_PresheafOfModules_PullbackMonoidal
-- name    : PresheafOfModules_PullbackMonoidal
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/31057c4a-214c-58d1-9dfd-6e08ca0c4df5
-- title:
--   Monoidal structure on pullback of presheaves of modules
-- statement:
--   Working with presheaves of modules over presheaves of rings obtained from presheaves of commutative rings by the forgetful functor, this module installs monoidal data on the restriction, pushforward and pullback functors. For a morphism $\varphi\colon S\to R$ of presheaves of commutative rings on a category $C$, `ringCatHom` is $\varphi$ whiskered into `RingCat`, and `restrictScalarsε`, `restrictScalarsμ` give the section-wise unit and multiplication maps of the induced restriction-of-scalars functor, taken at each $U$ from Mathlib's lax monoidal structure on `ModuleCat.restrictScalars` along $\varphi_U$; naturality in $U$ is checked on tensors, yielding `restrictScalars_laxMonoidal`. Since the pushforward along $F\colon C\to D$ with $\varphi\colon S\to F^{\mathrm{op}}\circ R$ factors as the transport of sections $M\mapsto(U\mapsto M(FU))$ followed by restriction of scalars, it is lax monoidal (`pushforward_laxMonoidal`), and whenever the pushforward has a left adjoint the pullback inherits an oplax monoidal structure from the adjunction (`pullback_oplaxMonoidal`). Separately, `freeεIso` and `freeμIso` exhibit, section by section, the isomorphisms $R\cong$ free module on a point and $\mathrm{Free}(F)\otimes\mathrm{Free}(G)\cong\mathrm{Free}(F\times G)$, making the free presheaf-of-modules functor on presheaves of types strong monoidal (`free_monoidal`), the monoidal structure on presheaves of types being the cartesian one. A general lemma `isIso_app_of_isColimit` states that a natural transformation of colimit-preserving functors which is invertible on a diagram is invertible at the apex of a colimit cocone.
--
--   The `PullbackMonoidal` section fixes small categories $C,D$ with finite products, a finite-product-preserving $F\colon C\to D$, and $\varphi\colon S\to F^{\mathrm{op}}\circ R$; `pf`, `pb`, `adj` abbreviate the pushforward, the pullback and their adjunction, and `gS U`, `gR V` the free modules on the Yoneda presheaves of $U$ and $V$. Using the corepresentability `h₂` of $\mathrm{Hom}(gS\,U,\,pf(-))$ by $gR(FU)$ and the resulting map `u₂`, `e` is an isomorphism $pb(gS\,U)\cong gR(F U)$, computed on the generator $\mathrm{freeMk}(\mathrm{id})$ by `u₂_app_freeMk`. The isomorphisms `yonedaTensorIso`, `tensorUnitIso` ($h_U\times h_V\cong h_{U\times V}$, $\mathbf{1}\cong h_{\top}$) give comparison isomorphisms `j`, `j₀` on the source side and `r`, `r₀` on the target side, the latter also using $F(U\times V)\cong FU\times FV$ and $F(\top)\cong\top$. The computations `keyL`, `keyR`, `keyL₀`, `keyR₀` evaluate both sides of the relevant squares on $\mathrm{freeMk}(\mathrm{id})$, giving `key_δ`, `key_η`, hence `δ_gS_comp` and `η_eq` expressing the oplax structure maps at free modules on representables as composites of isomorphisms, so that they are invertible. `isIso_app_of_freeYoneda` propagates invertibility from these generators to all presheaves of modules, using the presentation of an arbitrary module as a cokernel of a map of coproducts of free modules on representables together with preservation of colimits. Combining, $\delta$ and $\eta$ for the pullback are isomorphisms, and `pullback_monoidal`, `pullback_monoidal'` record that the pullback is strong monoidal.
--
--   **Relation to Mathlib.** Mathlib supplies the categories of presheaves of modules, the pullback–pushforward adjunction, the free presheaf-of-modules functor, the free-on-Yoneda presentation of a presheaf of modules, and the lax monoidal and free monoidal structures on `ModuleCat.restrictScalars` and `ModuleCat.free`; what is added here are the corresponding monoidal structures one level up, on restriction of scalars, pushforward, free and pullback for presheaves of modules.
--
--   **Where it is used.** This is general infrastructure for the sheaf-theoretic layer of the formalisation: it provides the presheaf-level statement that inverse image of modules along a morphism of ringed sites is compatible with tensor products and units, from which the corresponding statement for sheaves of modules is obtained by localisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_PresheafOfModules_PullbackMonoidal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe v u v₁ u₁ v₂ u₂

open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal Functor.OplaxMonoidal

namespace PresheafOfModules

section restrictScalars

variable {C : Type u₁} [Category.{v₁} C] {R S : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : S ⟶ R)

abbrev ringCatHom : S ⋙ forget₂ CommRingCat RingCat ⟶ R ⋙ forget₂ CommRingCat RingCat :=
  Functor.whiskerRight φ (forget₂ CommRingCat RingCat)

noncomputable abbrev restrictScalarsAt (U : Cᵒᵖ) : ModuleCat.{u} (R.obj U) ⥤ ModuleCat.{u} (S.obj U) :=
  ModuleCat.restrictScalars (φ.app U).hom

example (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) (U : Cᵒᵖ) :
    ((restrictScalars (ringCatHom φ)).obj M).obj U = (restrictScalarsAt φ U).obj (M.obj U) := rfl

noncomputable def restrictScalarsε :
    𝟙_ (PresheafOfModules.{u} (S ⋙ forget₂ _ _)) ⟶
      (restrictScalars (ringCatHom φ)).obj (𝟙_ (PresheafOfModules.{u} (R ⋙ forget₂ _ _))) where
  app U := ε (restrictScalarsAt φ U)
  naturality {U V} i := by
    refine ModuleCat.hom_ext (LinearMap.ext fun (s : S.obj U) => ?_)
    change ε (restrictScalarsAt φ V) (S.map i s) = R.map i (ε (restrictScalarsAt φ U) s)
    erw [ModuleCat.restrictScalars_η, ModuleCat.restrictScalars_η]
    exact ConcreteCategory.congr_hom (φ.naturality i) s

noncomputable def restrictScalarsμ (M N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) :
    (restrictScalars (ringCatHom φ)).obj M ⊗ (restrictScalars (ringCatHom φ)).obj N ⟶
      (restrictScalars (ringCatHom φ)).obj (M ⊗ N) where
  app U := μ (restrictScalarsAt φ U) (M.obj U) (N.obj U)
  naturality {U V} i := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    dsimp
    erw [Monoidal.tensorObj_map_tmul]
    erw [ModuleCat.restrictScalars_μ_tmul, ModuleCat.restrictScalars_μ_tmul]
    erw [Monoidal.tensorObj_map_tmul]
    rfl

noncomputable instance restrictScalars_laxMonoidal :
    (restrictScalars (ringCatHom φ)).LaxMonoidal where
  ε := restrictScalarsε φ
  μ M N := restrictScalarsμ φ M N
  μ_natural_left f N := by
    ext1 U
    simp only [comp_app, whiskerRight_app, restrictScalars_map_app]
    exact μ_natural_left (restrictScalarsAt φ U) (f.app U) (N.obj U)
  μ_natural_right M f := by
    ext1 U
    simp only [comp_app, whiskerLeft_app, restrictScalars_map_app]
    exact μ_natural_right (restrictScalarsAt φ U) (M.obj U) (f.app U)
  associativity M N P := by
    ext1 U
    simp only [comp_app, whiskerRight_app, whiskerLeft_app, restrictScalars_map_app,
      associator_hom_app]
    exact associativity (restrictScalarsAt φ U) (M.obj U) (N.obj U) (P.obj U)
  left_unitality M := by
    ext1 U
    simp only [comp_app, whiskerRight_app, restrictScalars_map_app, leftUnitor_hom_app]
    exact left_unitality (restrictScalarsAt φ U) (M.obj U)
  right_unitality M := by
    ext1 U
    simp only [comp_app, whiskerLeft_app, restrictScalars_map_app, rightUnitor_hom_app]
    exact right_unitality (restrictScalarsAt φ U) (M.obj U)

end restrictScalars

section pushforward

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
  {R : Dᵒᵖ ⥤ CommRingCat.{u}} {S : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : S ⟶ F.op ⋙ R)

noncomputable instance pushforward_laxMonoidal :
    (pushforward (R := R ⋙ forget₂ _ _) (ringCatHom φ)).LaxMonoidal :=
  inferInstanceAs (pushforward₀OfCommRingCat F R ⋙
    restrictScalars (ringCatHom (R := F.op ⋙ R) φ)).LaxMonoidal

noncomputable instance pullback_oplaxMonoidal
    [(pushforward (R := R ⋙ forget₂ _ _) (ringCatHom φ)).IsRightAdjoint] :
    (pullback (R := R ⋙ forget₂ _ _) (ringCatHom φ)).OplaxMonoidal :=
  (pullbackPushforwardAdjunction (R := R ⋙ forget₂ _ _) (ringCatHom φ)).leftAdjointOplaxMonoidal

end pushforward

end PresheafOfModules

namespace CategoryTheory.Limits

lemma isIso_app_of_isColimit {𝒜 : Type*} [Category 𝒜] {ℬ : Type*} [Category ℬ]
    {J : Type*} [Category J] {H₁ H₂ : 𝒜 ⥤ ℬ} (τ : H₁ ⟶ H₂) {K : J ⥤ 𝒜} {c : Cocone K}
    (hc : IsColimit c) [PreservesColimit K H₁] [PreservesColimit K H₂]
    (h : ∀ j, IsIso (τ.app (K.obj j))) : IsIso (τ.app c.pt) := by
  let hc₁ := isColimitOfPreserves H₁ hc
  let hc₂ := isColimitOfPreserves H₂ hc
  let s : Cocone (K ⋙ H₂) :=
    { pt := H₁.obj c.pt
      ι := { app := fun j => inv (τ.app (K.obj j)) ≫ H₁.map (c.ι.app j)
             naturality := fun j j' g => by
               dsimp
               rw [← cancel_epi (τ.app (K.obj j))]
               simp only [Category.comp_id, IsIso.hom_inv_id_assoc]
               rw [← τ.naturality_assoc, IsIso.hom_inv_id_assoc, ← H₁.map_comp, Cocone.w] } }
  refine ⟨hc₂.desc s, ?_, ?_⟩
  · apply hc₁.hom_ext
    intro j
    have := hc₂.fac s j
    dsimp [s] at this ⊢
    rw [Category.comp_id, τ.naturality_assoc, this, IsIso.hom_inv_id_assoc]
  · apply hc₂.hom_ext
    intro j
    have := hc₂.fac s j
    dsimp [s] at this ⊢
    rw [Category.comp_id, reassoc_of% this, τ.naturality, IsIso.inv_hom_id_assoc]

end CategoryTheory.Limits

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

local notation "R'" => R ⋙ forget₂ CommRingCat RingCat

lemma freeObj_map_freeMk (T : Cᵒᵖ ⥤ Type u) {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : T.obj X) :
    (freeObj (R := R') T).map f (ModuleCat.freeMk x) = ModuleCat.freeMk (T.map f x) := by
  simp [freeObj, ModuleCat.freeDesc_apply]

noncomputable def freeεIso :
    𝟙_ (PresheafOfModules.{u} R') ≅ (free R').obj (𝟙_ (Cᵒᵖ ⥤ Type u)) :=
  isoMk (fun X => ModuleCat.FreeMonoidal.εIso (R.obj X)) (by
    intro X Y f
    refine ModuleCat.hom_ext (LinearMap.ext fun (r : R.obj X) => ?_)
    have h1 : ∀ (Z : Cᵒᵖ) (s : R.obj Z), (ModuleCat.FreeMonoidal.εIso (R.obj Z)).hom s =
        s • ModuleCat.freeMk PUnit.unit := fun Z s => by
      have := (ModuleCat.FreeMonoidal.εIso (R.obj Z)).hom.hom.map_smul s (1 : R.obj Z)
      rw [smul_eq_mul, mul_one] at this
      exact this
    change (ModuleCat.FreeMonoidal.εIso (R.obj Y)).hom ((unit R').map f r) =
      ((free R').obj (𝟙_ (Cᵒᵖ ⥤ Type u))).map f
        ((ModuleCat.FreeMonoidal.εIso (R.obj X)).hom r)
    rw [h1, h1, PresheafOfModules.map_smul]
    erw [freeObj_map_freeMk]
    rfl)

noncomputable def freeμIso (F G : Cᵒᵖ ⥤ Type u) :
    (free R').obj F ⊗ (free R').obj G ≅ (free R').obj (F ⊗ G) :=
  isoMk (fun X => ModuleCat.FreeMonoidal.μIso (R.obj X) (F.obj X) (G.obj X)) (by
    intro X Y f
    rw [← cancel_epi (ModuleCat.FreeMonoidal.μIso (R.obj X) (F.obj X) (G.obj X)).inv,
      Iso.inv_hom_id_assoc]
    apply ModuleCat.free_hom_ext
    rintro ⟨x, y⟩
    change (ModuleCat.FreeMonoidal.μIso (R.obj Y) (F.obj Y) (G.obj Y)).hom
      (((free R').obj F ⊗ (free R').obj G).map f
        ((ModuleCat.FreeMonoidal.μIso (R.obj X) (F.obj X) (G.obj X)).inv (ModuleCat.freeMk (x, y)))) =
      ((free R').obj (F ⊗ G)).map f (ModuleCat.freeMk (x, y))
    erw [ModuleCat.FreeMonoidal.μIso_inv_freeMk]
    erw [Monoidal.tensorObj_map_tmul]
    erw [freeObj_map_freeMk, freeObj_map_freeMk, freeObj_map_freeMk]
    erw [ModuleCat.FreeMonoidal.μIso_hom_freeMk_tmul_freeMk]
    rfl)

@[simp] lemma freeμIso_hom_app (F G : Cᵒᵖ ⥤ Type u) (X : Cᵒᵖ) :
    (freeμIso (R := R) F G).hom.app X =
      (ModuleCat.FreeMonoidal.μIso (R.obj X) (F.obj X) (G.obj X)).hom := rfl
@[simp] lemma freeεIso_hom_app (X : Cᵒᵖ) :
    (freeεIso (R := R)).hom.app X = (ModuleCat.FreeMonoidal.εIso (R.obj X)).hom := rfl

noncomputable instance free_monoidal : (free R').Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := freeεIso
      μIso := freeμIso
      μIso_hom_natural_left := fun {F F'} f G => by
        ext1 X
        simp only [comp_app, whiskerRight_app, free_map_app, freeμIso_hom_app,
          Monoidal.whiskerRight_app]
        exact μ_natural_left (ModuleCat.free (R.obj X)) (f.app X) (G.obj X)
      μIso_hom_natural_right := fun {F F'} G f => by
        ext1 X
        simp only [comp_app, whiskerLeft_app, free_map_app, freeμIso_hom_app,
          Monoidal.whiskerLeft_app]
        exact μ_natural_right (ModuleCat.free (R.obj X)) (G.obj X) (f.app X)
      associativity := fun F G H => by
        ext1 X
        simp only [comp_app, whiskerRight_app, whiskerLeft_app, free_map_app, freeμIso_hom_app,
          associator_hom_app, Monoidal.associator_hom_app]
        exact associativity (ModuleCat.free (R.obj X)) (F.obj X) (G.obj X) (H.obj X)
      left_unitality := fun F => by
        ext1 X
        simp only [comp_app, whiskerRight_app, free_map_app, freeμIso_hom_app, freeεIso_hom_app,
          leftUnitor_hom_app, Monoidal.leftUnitor_hom_app]
        exact left_unitality (ModuleCat.free (R.obj X)) (F.obj X)
      right_unitality := fun F => by
        ext1 X
        simp only [comp_app, whiskerLeft_app, free_map_app, freeμIso_hom_app, freeεIso_hom_app,
          rightUnitor_hom_app, Monoidal.rightUnitor_hom_app]
        exact right_unitality (ModuleCat.free (R.obj X)) (F.obj X) }

end PresheafOfModules

namespace PresheafOfModules

namespace PullbackMonoidal

open Opposite Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  [HasFiniteProducts C] [HasFiniteProducts D]
  (F : C ⥤ D) [PreservesFiniteProducts F]
  {R : Dᵒᵖ ⥤ CommRingCat.{u}} {S : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : S ⟶ F.op ⋙ R)

local notation "R'" => R ⋙ forget₂ CommRingCat RingCat
local notation "S'" => S ⋙ forget₂ CommRingCat RingCat

noncomputable abbrev pf : PresheafOfModules.{u} R' ⥤ PresheafOfModules.{u} S' :=
  pushforward (R := R') (ringCatHom φ)

noncomputable abbrev pb : PresheafOfModules.{u} S' ⥤ PresheafOfModules.{u} R' :=
  pullback (R := R') (ringCatHom φ)

noncomputable abbrev adj : pb F φ ⊣ pf F φ := pullbackPushforwardAdjunction (R := R') (ringCatHom φ)

noncomputable abbrev gS (U : C) : PresheafOfModules.{u} S' := (free S').obj (yoneda.obj U)
noncomputable abbrev gR (V : D) : PresheafOfModules.{u} R' := (free R').obj (yoneda.obj V)

noncomputable abbrev h₂ (U : C) :
    (pf F φ ⋙ coyoneda.obj (op (gS U))).CorepresentableBy (gR (F.obj U)) :=
  pushforwardCompCoyonedaFreeYonedaCorepresentableBy (R := R') (ringCatHom φ) U

noncomputable def u₂ (U : C) : gS U ⟶ (pf F φ).obj (gR (F.obj U)) :=
  (h₂ F φ U).homEquiv (𝟙 _)

omit [HasFiniteProducts C] [HasFiniteProducts D] [PreservesFiniteProducts F] in
lemma freeYonedaEquiv_apply' {M : PresheafOfModules.{u} S'} {X : C}
    (f : gS X ⟶ M) : freeYonedaEquiv f = f.app (op X) (ModuleCat.freeMk (𝟙 X)) := rfl

omit [HasFiniteProducts C] [HasFiniteProducts D] [PreservesFiniteProducts F] in
lemma gS_map_freeMk {U W W' : C} (a : W ⟶ U) (b : W' ⟶ W) :
    (gS (S := S) U).map b.op (ModuleCat.freeMk a) = ModuleCat.freeMk (b ≫ a) := by
  erw [freeObj_map_freeMk]; simp

omit [HasFiniteProducts C] [HasFiniteProducts D] [PreservesFiniteProducts F] in
lemma gR_map_freeMk {U W W' : D} (a : W ⟶ U) (b : W' ⟶ W) :
    (gR (R := R) U).map b.op (ModuleCat.freeMk a) = ModuleCat.freeMk (b ≫ a) := by
  erw [freeObj_map_freeMk]; simp

omit [HasFiniteProducts C] [HasFiniteProducts D] [PreservesFiniteProducts F] in

lemma free_map_app_freeMk {E : Type u} [SmallCategory E] {T : Eᵒᵖ ⥤ CommRingCat.{u}}
    {P Q : Eᵒᵖ ⥤ Type u} (ψ : P ⟶ Q) (X : Eᵒᵖ) (x : P.obj X) :
    ((free (T ⋙ forget₂ CommRingCat RingCat)).map ψ).app X (ModuleCat.freeMk x) =
      (ModuleCat.freeMk (ψ.app X x) : ((free (T ⋙ forget₂ CommRingCat RingCat)).obj Q).obj X) := by
  simp
  exact ModuleCat.free_map_apply _ _

omit [HasFiniteProducts C] [HasFiniteProducts D] [PreservesFiniteProducts F] in

lemma freeμIso_inv_app_freeMk {E : Type u} [SmallCategory E] {T : Eᵒᵖ ⥤ CommRingCat.{u}}
    (P Q : Eᵒᵖ ⥤ Type u) (X : Eᵒᵖ) (z : (P ⊗ Q).obj X) :
    (freeμIso (R := T) P Q).inv.app X (ModuleCat.freeMk z) =
      (ModuleCat.freeMk z.1 ⊗ₜ[T.obj X] ModuleCat.freeMk z.2 :
        (((free (T ⋙ forget₂ CommRingCat RingCat)).obj P).obj X ⊗
          ((free (T ⋙ forget₂ CommRingCat RingCat)).obj Q).obj X :)) :=
  ModuleCat.FreeMonoidal.μIso_inv_freeMk _ z

omit [HasFiniteProducts C] [HasFiniteProducts D] [PreservesFiniteProducts F] in

lemma tensorHom_app_tmul {E : Type u} [SmallCategory E] {T : Eᵒᵖ ⥤ CommRingCat.{u}}
    {M₁ M₂ M₃ M₄ : PresheafOfModules.{u} (T ⋙ forget₂ CommRingCat RingCat)}
    (f : M₁ ⟶ M₂) (g : M₃ ⟶ M₄) (X : Eᵒᵖ) (m : M₁.obj X) (n : M₃.obj X) :
    DFunLike.coe (α := (M₁.obj X ⊗ M₃.obj X :)) (β := fun _ => (M₂.obj X ⊗ M₄.obj X :))
      ((f ⊗ₘ g).app X).hom (m ⊗ₜ[T.obj X] n) = f.app X m ⊗ₜ[T.obj X] g.app X n := by
  erw [PresheafOfModules.tensorHom_app]
  exact ModuleCat.MonoidalCategory.tensorHom_tmul _ _ _ _

omit [HasFiniteProducts C] [HasFiniteProducts D] [PreservesFiniteProducts F] in

lemma u₂_app_freeMk (U : C) {W : C} (a : W ⟶ U) :
    (u₂ F φ U).app (op W) (ModuleCat.freeMk a) =
      (ModuleCat.freeMk (F.map a) : (gR (R := R) (F.obj U)).obj (op (F.obj W))) := by
  have h1 : (u₂ F φ U).app (op U) (ModuleCat.freeMk (𝟙 U)) =
      (ModuleCat.freeMk (𝟙 (F.obj U)) : (gR (R := R) (F.obj U)).obj (op (F.obj U))) := by
    erw [freeYonedaEquiv_symm_app]; rfl
  have h2 := naturality_apply (u₂ F φ U) a.op (ModuleCat.freeMk (𝟙 U))
  rw [gS_map_freeMk, Category.comp_id] at h2
  rw [h2, h1]
  erw [pushforward_obj_map_apply]
  change (gR (R := R) (F.obj U)).map (F.map a).op (ModuleCat.freeMk (𝟙 (F.obj U))) = _
  rw [gR_map_freeMk, Category.comp_id]

noncomputable def e (U : C) : (pb F φ).obj (gS U) ≅ gR (F.obj U) where
  hom := ((adj F φ).homEquiv _ _).symm (u₂ F φ U)
  inv := (h₂ F φ U).homEquiv.symm ((adj F φ).unit.app (gS U))
  hom_inv_id := ((adj F φ).homEquiv _ _).injective (by
    rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
    have := (h₂ F φ U).homEquiv_comp ((h₂ F φ U).homEquiv.symm ((adj F φ).unit.app (gS U))) (𝟙 _)
    rw [Category.id_comp, Equiv.apply_symm_apply] at this

    erw [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id, Category.comp_id]
    exact this.symm)
  inv_hom_id := (h₂ F φ U).homEquiv.injective (by
    rw [(h₂ F φ U).homEquiv_comp, Equiv.apply_symm_apply]
    change (adj F φ).unit.app (gS U) ≫ (pf F φ).map (((adj F φ).homEquiv _ _).symm (u₂ F φ U)) =
      (h₂ F φ U).homEquiv (𝟙 _)
    erw [← (adj F φ).homEquiv_unit, Equiv.apply_symm_apply]
    rfl)

lemma unit_comp_map_e_hom (U : C) :
    (adj F φ).unit.app (gS U) ≫ (pf F φ).map (e F φ U).hom = u₂ F φ U := by
  change (adj F φ).unit.app (gS U) ≫ (pf F φ).map (((adj F φ).homEquiv _ _).symm (u₂ F φ U)) = _
  erw [← (adj F φ).homEquiv_unit, Equiv.apply_symm_apply]

noncomputable def yonedaTensorIso {E : Type u} [SmallCategory E] [HasFiniteProducts E] (U V : E) :
    yoneda.obj U ⊗ yoneda.obj V ≅ yoneda.obj (U ⨯ V) :=
  NatIso.ofComponents (fun W => Equiv.toIso
    { toFun := fun p => prod.lift p.1 p.2
      invFun := fun c => (c ≫ prod.fst, c ≫ prod.snd)
      left_inv := fun p => Prod.ext (prod.lift_fst _ _) (prod.lift_snd _ _)
      right_inv := fun c => by apply Limits.prod.hom_ext <;> simp }) (by
    intro W W' f
    ext p
    change prod.lift ((yoneda.obj U ⊗ yoneda.obj V).map f p).1
        ((yoneda.obj U ⊗ yoneda.obj V).map f p).2 = f.unop ≫ prod.lift p.1 p.2
    erw [Monoidal.tensorObj_map, tensor_apply]
    apply Limits.prod.hom_ext <;> simp)

lemma yonedaTensorIso_inv_app_apply {E : Type u} [SmallCategory E] [HasFiniteProducts E] (U V : E)
    {W : E} (c : W ⟶ U ⨯ V) :
    (yonedaTensorIso U V).inv.app (op W) c = (c ≫ prod.fst, c ≫ prod.snd) := rfl

noncomputable def tensorUnitIso (E : Type u) [SmallCategory E] [HasFiniteProducts E] :
    𝟙_ (Eᵒᵖ ⥤ Type u) ≅ yoneda.obj (⊤_ E) :=
  NatIso.ofComponents (fun W => Equiv.toIso
    { toFun := fun _ => terminal.from _
      invFun := fun _ => PUnit.unit
      left_inv := fun _ => rfl
      right_inv := fun c => (terminal.hom_ext _ _) }) (by
    intro W W' f; ext p; apply terminal.hom_ext)

noncomputable def j (U V : C) : gS (S := S) U ⊗ gS V ≅ gS (U ⨯ V) :=
  freeμIso (yoneda.obj U) (yoneda.obj V) ≪≫ (free S').mapIso (yonedaTensorIso U V)

noncomputable def j₀ : 𝟙_ (PresheafOfModules.{u} S') ≅ gS (S := S) (⊤_ C) :=
  freeεIso ≪≫ (free S').mapIso (tensorUnitIso C)

noncomputable def r (U V : C) : gR (R := R) (F.obj (U ⨯ V)) ≅ gR (F.obj U) ⊗ gR (F.obj V) :=
  (free R').mapIso (yoneda.mapIso (PreservesLimitPair.iso F U V)) ≪≫
    ((free R').mapIso (yonedaTensorIso (F.obj U) (F.obj V))).symm ≪≫
    (freeμIso (yoneda.obj (F.obj U)) (yoneda.obj (F.obj V))).symm

noncomputable def r₀ : gR (R := R) (F.obj (⊤_ C)) ≅ 𝟙_ _ :=
  (free R').mapIso (yoneda.mapIso (PreservesTerminal.iso F)) ≪≫
    ((free R').mapIso (tensorUnitIso D)).symm ≪≫ freeεIso.symm

omit [HasFiniteProducts C] [HasFiniteProducts D] [PreservesFiniteProducts F] in

lemma pf_μ_app_tmul (M N : PresheafOfModules.{u} R') (W : C)
    (m : M.obj (op (F.obj W))) (n : N.obj (op (F.obj W))) :
    DFunLike.coe (α := (((pf F φ).obj M).obj (op W) ⊗ ((pf F φ).obj N).obj (op W) :))
      (β := fun _ => ((pf F φ).obj (M ⊗ N)).obj (op W))
      ((μ (pf F φ) M N).app (op W)).hom (m ⊗ₜ[S.obj (op W)] n) = m ⊗ₜ[R.obj (op (F.obj W))] n := by
  change DFunLike.coe (α := (((pf F φ).obj M).obj (op W) ⊗ ((pf F φ).obj N).obj (op W) :))
      (β := fun _ => ((pf F φ).obj (M ⊗ N)).obj (op W))
    ((μ (restrictScalars (ringCatHom (R := F.op ⋙ R) φ))
        ((pushforward₀OfCommRingCat F R).obj M) ((pushforward₀OfCommRingCat F R).obj N) ≫
      (restrictScalars (ringCatHom (R := F.op ⋙ R) φ)).map
        (μ (pushforward₀OfCommRingCat F R) M N)).app (op W)).hom (m ⊗ₜ[S.obj (op W)] n) = _
  rw [show μ (pushforward₀OfCommRingCat F R) M N = 𝟙 _ from rfl, CategoryTheory.Functor.map_id,
    Category.comp_id]
  exact ModuleCat.restrictScalars_μ_tmul _ _ _ m n

lemma keyL (U V : C) :
    ((j (S := S) U V).inv ≫ ((u₂ F φ U ⊗ₘ u₂ F φ V) ≫
      μ (pf F φ) (gR (F.obj U)) (gR (F.obj V)))).app (op (U ⨯ V)) (ModuleCat.freeMk (𝟙 (U ⨯ V))) =
    (ModuleCat.freeMk (F.map prod.fst) ⊗ₜ[R.obj (op (F.obj (U ⨯ V)))]
      ModuleCat.freeMk (F.map prod.snd) :
      ((gR (R := R) (F.obj U)).obj (op (F.obj (U ⨯ V))) ⊗
        (gR (R := R) (F.obj V)).obj (op (F.obj (U ⨯ V))) :)) := by
  change (μ (pf F φ) (gR (F.obj U)) (gR (F.obj V))).app (op (U ⨯ V))
    (((u₂ F φ U ⊗ₘ u₂ F φ V).app (op (U ⨯ V)))
      ((freeμIso (yoneda.obj U) (yoneda.obj V)).inv.app (op (U ⨯ V))
        (((free S').map (yonedaTensorIso U V).inv).app (op (U ⨯ V))
          (ModuleCat.freeMk (𝟙 (U ⨯ V)))))) = _
  erw [free_map_app_freeMk, yonedaTensorIso_inv_app_apply, freeμIso_inv_app_freeMk]
  erw [tensorHom_app_tmul]
  erw [u₂_app_freeMk, u₂_app_freeMk]
  erw [pf_μ_app_tmul]
  simp only [Category.id_comp]

lemma keyR (U V : C) :
    (u₂ F φ (U ⨯ V) ≫ (pf F φ).map (r (R := R) F U V).hom).app (op (U ⨯ V))
      (ModuleCat.freeMk (𝟙 (U ⨯ V))) =
    (ModuleCat.freeMk (F.map prod.fst) ⊗ₜ[R.obj (op (F.obj (U ⨯ V)))]
      ModuleCat.freeMk (F.map prod.snd) :
      ((gR (R := R) (F.obj U)).obj (op (F.obj (U ⨯ V))) ⊗
        (gR (R := R) (F.obj V)).obj (op (F.obj (U ⨯ V))) :)) := by
  change ((pf F φ).map (r (R := R) F U V).hom).app (op (U ⨯ V))
    ((u₂ F φ (U ⨯ V)).app (op (U ⨯ V)) (ModuleCat.freeMk (𝟙 (U ⨯ V)))) = _
  erw [u₂_app_freeMk]
  erw [pushforward_map_app_apply]
  change (freeμIso (yoneda.obj (F.obj U)) (yoneda.obj (F.obj V))).inv.app (op (F.obj (U ⨯ V)))
    (((free R').map (yonedaTensorIso (F.obj U) (F.obj V)).inv).app (op (F.obj (U ⨯ V)))
      (((free R').map (yoneda.map (PreservesLimitPair.iso F U V).hom)).app (op (F.obj (U ⨯ V)))
        (ModuleCat.freeMk (F.map (𝟙 (U ⨯ V)))))) = _
  erw [free_map_app_freeMk, free_map_app_freeMk, yonedaTensorIso_inv_app_apply,
    freeμIso_inv_app_freeMk]
  change ModuleCat.freeMk ((F.map (𝟙 (U ⨯ V)) ≫ (PreservesLimitPair.iso F U V).hom) ≫ prod.fst)
      ⊗ₜ[R.obj (op (F.obj (U ⨯ V)))]
    ModuleCat.freeMk ((F.map (𝟙 (U ⨯ V)) ≫ (PreservesLimitPair.iso F U V).hom) ≫ prod.snd) = _
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc,
    PreservesLimitPair.iso_hom, prodComparison_fst, prodComparison_snd]

lemma key_δ (U V : C) :
    (j (S := S) U V).inv ≫ ((u₂ F φ U ⊗ₘ u₂ F φ V) ≫
      μ (pf F φ) (gR (F.obj U)) (gR (F.obj V))) =
      u₂ F φ (U ⨯ V) ≫ (pf F φ).map (r (R := R) F U V).hom := by
  apply freeYonedaEquiv.injective
  rw [freeYonedaEquiv_apply', freeYonedaEquiv_apply', keyL, keyR]

lemma δ_gS_comp (U V : C) :
    δ (pb F φ) (gS U) (gS V) ≫ ((e F φ U).hom ⊗ₘ (e F φ V).hom) =
      (pb F φ).map (j (S := S) U V).hom ≫ (e F φ (U ⨯ V)).hom ≫ (r (R := R) F U V).hom := by
  apply ((adj F φ).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  erw [Adjunction.leftAdjointOplaxMonoidal_δ, Equiv.apply_symm_apply]
  rw [Category.assoc, ← Functor.LaxMonoidal.μ_natural, tensorHom_comp_tensorHom_assoc,
    unit_comp_map_e_hom, unit_comp_map_e_hom,
    Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_unit, unit_comp_map_e_hom,
    ← cancel_epi (j (S := S) U V).inv, Iso.inv_hom_id_assoc]
  exact key_δ F φ U V

instance isIso_δ_gS (U V : C) : IsIso (δ (pb F φ) (gS U) (gS V)) := by
  have h : δ (pb F φ) (gS U) (gS V) =
      ((pb F φ).map (j (S := S) U V).hom ≫ (e F φ (U ⨯ V)).hom ≫ (r (R := R) F U V).hom) ≫
        inv ((e F φ U).hom ⊗ₘ (e F φ V).hom) := by
    rw [← δ_gS_comp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [h]
  infer_instance

omit [HasFiniteProducts C] [HasFiniteProducts D] [PreservesFiniteProducts F] in

lemma isIso_app_of_freeYoneda {ℬ : Type*} [Category ℬ]
    {H₁ H₂ : PresheafOfModules.{u} S' ⥤ ℬ}
    [PreservesColimitsOfSize.{u, u} H₁] [PreservesColimitsOfSize.{u, u} H₂] (τ : H₁ ⟶ H₂)
    (h : ∀ U : C, IsIso (τ.app (gS U))) (M : PresheafOfModules.{u} S') : IsIso (τ.app M) := by
  have hcop : ∀ (N : PresheafOfModules.{u} S'), IsIso (τ.app N.freeYonedaCoproduct) := fun N =>
    isIso_app_of_isColimit τ (coproductIsCoproduct (Elements.freeYoneda (M := N)))
      (fun m => h m.as.1.unop)
  have : PreservesColimitsOfSize.{0, 0} H₁ := preservesSmallestColimits_of_preservesColimits H₁
  have : PreservesColimitsOfSize.{0, 0} H₂ := preservesSmallestColimits_of_preservesColimits H₂
  exact isIso_app_of_isColimit τ M.isColimitFreeYonedaCoproductsCokernelCofork
    (by rintro (_ | _) <;> exact hcop _)

instance : PreservesColimitsOfSize.{u, u} (pb F φ) := (adj F φ).leftAdjoint_preservesColimits

instance isIso_δ (A B : PresheafOfModules.{u} S') : IsIso (δ (pb F φ) A B) := by

  have h1 : ∀ (U : C) (B : PresheafOfModules.{u} S'), IsIso (δ (pb F φ) (gS U) B) := fun U => by
    let σ : tensorLeft (gS (S := S) U) ⋙ pb F φ ⟶ pb F φ ⋙ tensorLeft ((pb F φ).obj (gS U)) :=
      { app := fun B => δ (pb F φ) (gS U) B
        naturality := fun B B' g => (δ_natural_right (pb F φ) (gS U) g).symm }
    exact isIso_app_of_freeYoneda (S := S) σ (fun V => isIso_δ_gS F φ U V)

  let τ : tensorRight B ⋙ pb F φ ⟶ pb F φ ⋙ tensorRight ((pb F φ).obj B) :=
    { app := fun A => δ (pb F φ) A B
      naturality := fun A A' f => (δ_natural_left (pb F φ) f B).symm }
  exact isIso_app_of_freeYoneda (S := S) τ (fun U => h1 U B) A

omit [HasFiniteProducts D] [PreservesFiniteProducts F] in
lemma keyL₀ : ((j₀ (S := S)).inv ≫ ε (pf F φ)).app (op (⊤_ C))
      (ModuleCat.freeMk (𝟙 (⊤_ C))) = (1 : R.obj (op (F.obj (⊤_ C)))) := by
  change (ε (pf F φ)).app (op (⊤_ C)) ((freeεIso (R := S)).inv.app (op (⊤_ C))
    (((free S').map (tensorUnitIso C).inv).app (op (⊤_ C)) (ModuleCat.freeMk (𝟙 (⊤_ C))))) = _
  erw [free_map_app_freeMk]
  erw [ModuleCat.FreeMonoidal.εIso_inv_freeMk]

  change (ε (restrictScalars (ringCatHom (R := F.op ⋙ R) φ)) ≫
      (restrictScalars (ringCatHom (R := F.op ⋙ R) φ)).map
        (ε (pushforward₀OfCommRingCat F R))).app (op (⊤_ C)) (1 : S.obj (op (⊤_ C))) = _
  rw [show ε (pushforward₀OfCommRingCat F R) = 𝟙 _ from rfl, CategoryTheory.Functor.map_id,
    Category.comp_id]
  erw [ModuleCat.restrictScalars_η]
  exact (φ.app (op (⊤_ C))).hom.map_one

lemma keyR₀ : (u₂ F φ (⊤_ C) ≫ (pf F φ).map (r₀ (R := R) F).hom).app (op (⊤_ C))
      (ModuleCat.freeMk (𝟙 (⊤_ C))) = (1 : R.obj (op (F.obj (⊤_ C)))) := by
  change ((pf F φ).map (r₀ (R := R) F).hom).app (op (⊤_ C))
    ((u₂ F φ (⊤_ C)).app (op (⊤_ C)) (ModuleCat.freeMk (𝟙 (⊤_ C)))) = _
  erw [u₂_app_freeMk]
  erw [pushforward_map_app_apply]
  change (freeεIso (R := R)).inv.app (op (F.obj (⊤_ C)))
    (((free R').map (tensorUnitIso D).inv).app (op (F.obj (⊤_ C)))
      (((free R').map (yoneda.map (PreservesTerminal.iso F).hom)).app (op (F.obj (⊤_ C)))
        (ModuleCat.freeMk (F.map (𝟙 (⊤_ C)))))) = _
  erw [free_map_app_freeMk, free_map_app_freeMk]
  exact ModuleCat.FreeMonoidal.εIso_inv_freeMk _ _

lemma key_η : (j₀ (S := S)).inv ≫ ε (pf F φ) = u₂ F φ (⊤_ C) ≫ (pf F φ).map (r₀ (R := R) F).hom := by
  apply freeYonedaEquiv.injective
  rw [freeYonedaEquiv_apply', freeYonedaEquiv_apply', keyL₀, keyR₀]

lemma η_eq : η (pb F φ) = (pb F φ).map (j₀ (S := S)).hom ≫ (e F φ (⊤_ C)).hom ≫ (r₀ (R := R) F).hom := by
  apply ((adj F φ).homEquiv _ _).injective
  erw [Adjunction.leftAdjointOplaxMonoidal_η, Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_unit, unit_comp_map_e_hom,
    ← cancel_epi (j₀ (S := S)).inv, Iso.inv_hom_id_assoc]
  exact key_η F φ

instance isIso_η : IsIso (η (pb F φ)) := by rw [η_eq]; infer_instance

noncomputable instance pullback_monoidal : (pb F φ).Monoidal := Functor.Monoidal.ofOplaxMonoidal _

end PullbackMonoidal

noncomputable instance pullback_monoidal' {C D : Type u} [SmallCategory C] [SmallCategory D]
    [HasFiniteProducts C] [HasFiniteProducts D] (F : C ⥤ D) [PreservesFiniteProducts F]
    {R : Dᵒᵖ ⥤ CommRingCat.{u}} {S : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : S ⟶ F.op ⋙ R) :
    (pullback (R := R ⋙ forget₂ _ _) (ringCatHom φ)).Monoidal :=
  PullbackMonoidal.pullback_monoidal F φ

end PresheafOfModules


