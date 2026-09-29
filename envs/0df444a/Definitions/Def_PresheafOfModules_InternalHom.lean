-- Prove2me | Definitions.Def_PresheafOfModules_InternalHom
-- name    : PresheafOfModules_InternalHom
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/bad3bc55-e2e9-5f71-adc8-2cbdfb18224e
-- title:
--   Internal Hom of presheaves of modules; monoidal closedness
-- statement:
--   Fix a category $C$, a presheaf of commutative rings $R \colon C^{\mathrm{op}} \to \mathbf{CommRing}$, and presheaves of $R$-modules $F, N$. For an object $X$ of $C^{\mathrm{op}}$, `PiFamily F N X` is the type of families $\varphi$ assigning to every arrow $f \colon X \to Y$ of $C^{\mathrm{op}}$ an $R(Y)$-linear map $\varphi_f \colon F(Y) \to N(Y)$; the predicate `IsNatural` asserts $N(g)(\varphi_f(x)) = \varphi_{f \circ g}(F(g)(x))$ for all $f \colon X \to Y$, $g \colon Y \to Z$ and $x \in F(Y)$, and `naturalFamilies F N X` is the additive subgroup of families satisfying it — that is, the module of $R|_X$-linear maps $F|_X \to N|_X$ over the slice. It carries the $R(X)$-module structure $(r \cdot \varphi)_f = R(f)(r) \cdot \varphi_f$, and restriction along $h \colon X \to X'$ sends $\varphi$ to $f \mapsto \varphi_{h \circ f}$ (`restrict`), making `InternalHom.presheaf F N` a presheaf of abelian groups which, with these module structures, is the presheaf of modules `ihomObj F N`. Postcomposition with $\psi \colon N \to N'$ gives `ihomMap` and hence the functor `ihomFunctor F` in the second variable.
--
--   The second half, stated for $C$ and the rings in a single universe, constructs the tensor–hom adjunction for the sectionwise tensor product. For $\theta \colon F \otimes G \to N$, `curryFamily` sends $y \in G(X)$ to the family $f \mapsto (x \mapsto \theta_Y(x \otimes G(f)(y)))$, giving `curry' F θ : G ⟶ ihomObj F N`; conversely `uncurry'` sends $\kappa$ to the map determined by $x \otimes y \mapsto (\kappa_X(y))_{\mathrm{id}_X}(x)$. The two constructions are mutually inverse (`uncurry'_curry'`, `curry'_uncurry'`), yielding `tensorIhomAdj F : tensorLeft F ⊣ ihomFunctor F` and the instance that presheaves of $R$-modules form a monoidal closed category.
--
--   **Relation to Mathlib.** Mathlib provides the sectionwise tensor product and monoidal structure on `PresheafOfModules`, but no internal Hom for presheaves of modules; this module supplies it together with the resulting `MonoidalClosed` instance.
--
--   **Where it is used.** The internal Hom and the adjunction are the input for the closed symmetric monoidal structure on sheaves of modules on a ringed site, hence for tensor products and duals of invertible sheaves and the group structure on Picard groups and on the relative Picard functor used in the geometric parts of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_PresheafOfModules_InternalHom.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v' u'

open CategoryTheory MonoidalCategory Limits Opposite

namespace PresheafOfModules

section general

variable {C : Type u'} [Category.{v'} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (F N : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

namespace InternalHom

lemma map_id_apply (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) (X : Cᵒᵖ) (x : M.obj X) :
    M.map (𝟙 X) x = x := by
  change (M.presheaf.map (𝟙 X)) x = x
  rw [M.presheaf.map_id]; rfl

abbrev PiFamily (X : Cᵒᵖ) : Type (max u u' v') :=
  ∀ ⦃Y : Cᵒᵖ⦄ (_ : X ⟶ Y), (F.obj Y →ₗ[R.obj Y] N.obj Y)

variable {F N} in

def IsNatural {X : Cᵒᵖ} (φ : PiFamily F N X) : Prop :=
  ∀ ⦃Y Z : Cᵒᵖ⦄ (f : X ⟶ Y) (g : Y ⟶ Z) (x : F.obj Y), N.map g (φ f x) = φ (f ≫ g) (F.map g x)

def naturalFamilies (X : Cᵒᵖ) : AddSubgroup (PiFamily F N X) where
  carrier := {φ | IsNatural φ}
  zero_mem' := by
    intro Y Z f g x
    simp only [Pi.zero_apply, LinearMap.zero_apply]
    exact (N.map g).hom.map_zero
  add_mem' := by
    intro φ ψ hφ hψ Y Z f g x
    simp only [Pi.add_apply, LinearMap.add_apply, map_add, hφ f g x, hψ f g x]
  neg_mem' := by
    intro φ hφ Y Z f g x
    simp only [Pi.neg_apply, LinearMap.neg_apply, map_neg, hφ f g x]

variable {F N}

@[ext] lemma naturalFamilies_ext {X : Cᵒᵖ} {φ ψ : naturalFamilies F N X}
    (h : ∀ ⦃Y : Cᵒᵖ⦄ (f : X ⟶ Y) (x : F.obj Y), φ.1 f x = ψ.1 f x) : φ = ψ :=
  Subtype.ext (funext fun _ => funext fun f => LinearMap.ext (h f))

lemma naturality {X : Cᵒᵖ} (φ : naturalFamilies F N X) ⦃Y Z : Cᵒᵖ⦄ (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : F.obj Y) : N.map g (φ.1 f x) = φ.1 (f ≫ g) (F.map g x) := φ.2 f g x

lemma congr_app {X : Cᵒᵖ} (φ : naturalFamilies F N X) {Y : Cᵒᵖ} {f g : X ⟶ Y} (h : f = g)
    (x : F.obj Y) : φ.1 f x = φ.1 g x := by subst h; rfl

instance (X : Cᵒᵖ) : SMul (R.obj X) (naturalFamilies F N X) where
  smul r φ := ⟨fun Y f => R.map f r • φ.1 f, by
    intro Y Z f g x
    simp only [LinearMap.smul_apply]
    rw [N.map_smul]
    erw [φ.2 f g x]
    congr 1
    rw [Functor.map_comp]
    rfl⟩

@[simp] lemma smul_app {X : Cᵒᵖ} (r : R.obj X) (φ : naturalFamilies F N X) {Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : F.obj Y) : (r • φ).1 f x = R.map f r • φ.1 f x := rfl
@[simp] lemma add_app {X : Cᵒᵖ} (φ ψ : naturalFamilies F N X) {Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : F.obj Y) : (φ + ψ).1 f x = φ.1 f x + ψ.1 f x := rfl
@[simp] lemma zero_app {X : Cᵒᵖ} {Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : F.obj Y) : (0 : naturalFamilies F N X).1 f x = 0 := rfl
@[simp] lemma neg_app {X : Cᵒᵖ} (φ : naturalFamilies F N X) {Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : F.obj Y) : (-φ).1 f x = - φ.1 f x := rfl
@[simp] lemma sub_app {X : Cᵒᵖ} (φ ψ : naturalFamilies F N X) {Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : F.obj Y) : (φ - ψ).1 f x = φ.1 f x - ψ.1 f x := rfl

instance (X : Cᵒᵖ) : Module (R.obj X) (naturalFamilies F N X) where
  one_smul φ := by ext Y f x; simp
  mul_smul r s φ := by ext Y f x; simp [mul_smul]
  smul_zero r := by ext Y f x; simp
  smul_add r φ ψ := by ext Y f x; simp
  add_smul r s φ := by ext Y f x; simp [add_smul]
  zero_smul φ := by ext Y f x; simp

variable (F N)

def restrict {X X' : Cᵒᵖ} (h : X ⟶ X') : naturalFamilies F N X →+ naturalFamilies F N X' where
  toFun φ := ⟨fun Y f => φ.1 (h ≫ f), fun Y Z f g x => by
    rw [φ.2 (h ≫ f) g x, Category.assoc]⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] lemma restrict_app {X X' : Cᵒᵖ} (h : X ⟶ X') (φ : naturalFamilies F N X) {Y : Cᵒᵖ}
    (f : X' ⟶ Y) (x : F.obj Y) : (restrict F N h φ).1 f x = φ.1 (h ≫ f) x := rfl

@[simps obj] def presheaf : Cᵒᵖ ⥤ Ab.{max u u' v'} where
  obj X := AddCommGrpCat.of (naturalFamilies F N X)
  map h := AddCommGrpCat.ofHom (restrict F N h)
  map_id X := by
    ext φ Y f x
    change φ.1 (𝟙 X ≫ f) x = φ.1 f x
    rw [Category.id_comp]
  map_comp h h' := by
    ext φ Y f x
    change φ.1 ((h ≫ h') ≫ f) x = φ.1 (h ≫ (h' ≫ f)) x
    rw [Category.assoc]

@[simp] lemma presheaf_map_apply {X X' : Cᵒᵖ} (h : X ⟶ X') (φ : naturalFamilies F N X) {Y : Cᵒᵖ}
    (f : X' ⟶ Y) (x : F.obj Y) : ((presheaf F N).map h φ).1 f x = φ.1 (h ≫ f) x := rfl

instance (X : Cᵒᵖ) : Module ((R ⋙ forget₂ CommRingCat RingCat).obj X) ((presheaf F N).obj X) :=
  inferInstanceAs (Module (R.obj X) (naturalFamilies F N X))

variable {N} in

def postcomp {N' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (ψ : N ⟶ N') (X : Cᵒᵖ) :
    naturalFamilies F N X →+ naturalFamilies F N' X where
  toFun φ := ⟨fun Y f =>
    { toFun := fun x => ψ.app Y (φ.1 f x)
      map_add' := fun x x' => by simp
      map_smul' := fun r x => by
        rw [(φ.1 f).map_smul]
        exact (ψ.app Y).hom.map_smul r _ }, by
    intro Y Z f g x
    change N'.map g (ψ.app Y (φ.1 f x)) = ψ.app Z (φ.1 (f ≫ g) (F.map g x))
    rw [← naturality_apply, φ.2 f g x]⟩
  map_zero' := by ext Y f x; exact (ψ.app Y).hom.map_zero
  map_add' φ φ' := by ext Y f x; exact (ψ.app Y).hom.map_add _ _

@[simp] lemma postcomp_app {N' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (ψ : N ⟶ N') {X : Cᵒᵖ}
    (φ : naturalFamilies F N X) {Y : Cᵒᵖ} (f : X ⟶ Y) (x : F.obj Y) :
    (postcomp F ψ X φ).1 f x = ψ.app Y (φ.1 f x) := rfl

end InternalHom

open InternalHom

@[simps! obj] noncomputable def ihomObj : PresheafOfModules.{max u u' v'} (R ⋙ forget₂ _ _) :=
  ofPresheaf (InternalHom.presheaf F N) (by
    intro X X' h r φ
    apply naturalFamilies_ext
    intro Y f x
    change (R.map (h ≫ f) r) • φ.1 (h ≫ f) x = R.map f (R.map h r) • φ.1 (h ≫ f) x
    rw [Functor.map_comp]
    rfl)

@[simp] lemma ihomObj_map_val {X X' : Cᵒᵖ} (h : X ⟶ X') (φ : (ihomObj F N).obj X) {Y : Cᵒᵖ}
    (f : X' ⟶ Y) (x : F.obj Y) :
    ((ihomObj F N).map h φ).1 f x = φ.1 (h ≫ f) x := rfl

variable {N} in

noncomputable def ihomMap {N' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (ψ : N ⟶ N') :
    ihomObj F N ⟶ ihomObj F N' :=
  homMk { app := fun X => AddCommGrpCat.ofHom (postcomp F ψ X)
          naturality := fun {X X'} h => by ext φ; rfl } (by
    intro X r φ
    apply naturalFamilies_ext
    intro Y f x
    exact (ψ.app Y).hom.map_smul _ _)

@[simp] lemma ihomMap_app_val {N' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (ψ : N ⟶ N')
    {X : Cᵒᵖ} (φ : (ihomObj F N).obj X) {Y : Cᵒᵖ} (f : X ⟶ Y) (x : F.obj Y) :
    ((ihomMap F ψ).app X φ).1 f x = ψ.app Y (φ.1 f x) := rfl

noncomputable def ihomFunctor :
    PresheafOfModules.{u} (R ⋙ forget₂ _ _) ⥤ PresheafOfModules.{max u u' v'} (R ⋙ forget₂ _ _) where
  obj N := ihomObj F N
  map ψ := ihomMap F ψ
  map_id N := by
    ext X φ
    apply naturalFamilies_ext
    intro Y f y; rfl
  map_comp ψ ψ' := by
    ext X φ
    apply naturalFamilies_ext
    intro Y f y; rfl

@[simp] lemma ihomFunctor_obj (N' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) :
    (ihomFunctor F).obj N' = ihomObj F N' := rfl
@[simp] lemma ihomFunctor_map {N' N'' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (ψ : N' ⟶ N'') :
    (ihomFunctor F).map ψ = ihomMap F ψ := rfl

end general

section closed

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (F : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) {G N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)}

namespace InternalHom

noncomputable def curryFamily (θ : F ⊗ G ⟶ N) {X : Cᵒᵖ} (y : G.obj X) : naturalFamilies F N X :=
  ⟨fun Y f =>
    { toFun := fun x => θ.app Y (x ⊗ₜ[R.obj Y] G.map f y)
      map_add' := fun x x' => by rw [TensorProduct.add_tmul, map_add]
      map_smul' := fun r x => by
        rw [RingHom.id_apply, ← (θ.app Y).hom.map_smul]
        rfl }, by
    intro Y Z f g x
    change N.map g (θ.app Y _) = θ.app Z _
    rw [← naturality_apply]
    erw [Monoidal.tensorObj_map_tmul]
    rw [← PresheafOfModules.map_comp_apply]⟩

@[simp] lemma curryFamily_app (θ : F ⊗ G ⟶ N) {X : Cᵒᵖ} (y : G.obj X) {Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : F.obj Y) : (curryFamily F θ y).1 f x = θ.app Y (x ⊗ₜ[R.obj Y] G.map f y) := rfl

end InternalHom

open InternalHom

noncomputable def curry' (θ : F ⊗ G ⟶ N) : G ⟶ ihomObj F N :=
  homMk
    { app := fun X => AddCommGrpCat.ofHom
        { toFun := fun y => curryFamily F θ y
          map_zero' := by
            apply naturalFamilies_ext; intro Y f x
            have h0 : G.map f (0 : G.obj X) = 0 := (G.map f).hom.map_zero
            rw [curryFamily_app, h0, TensorProduct.tmul_zero]
            exact (θ.app Y).hom.map_zero
          map_add' := fun y y' => by
            apply naturalFamilies_ext; intro Y f x
            have h1 : G.map f (y + y') = G.map f y + G.map f y' := (G.map f).hom.map_add _ _
            rw [InternalHom.add_app, curryFamily_app, curryFamily_app, curryFamily_app, h1,
              TensorProduct.tmul_add]
            exact (θ.app Y).hom.map_add _ _ }
      naturality := fun {X X'} h => by
        ext y
        apply naturalFamilies_ext; intro Y f x
        change θ.app Y (x ⊗ₜ[R.obj Y] G.map f (G.map h y)) = θ.app Y (x ⊗ₜ[R.obj Y] G.map (h ≫ f) y)
        rw [PresheafOfModules.map_comp_apply] }
    (by
      intro X r y
      apply naturalFamilies_ext; intro Y f x
      change θ.app Y (x ⊗ₜ[R.obj Y] G.map f (r • y)) = R.map f r • θ.app Y (x ⊗ₜ[R.obj Y] G.map f y)
      rw [G.map_smul]
      change θ.app Y (x ⊗ₜ[R.obj Y] ((R.map f r : R.obj Y) • G.map f y)) = _
      rw [TensorProduct.tmul_smul]
      exact (θ.app Y).hom.map_smul _ _)

@[simp] lemma curry'_app_val (θ : F ⊗ G ⟶ N) {X : Cᵒᵖ} (y : G.obj X) {Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : F.obj Y) : ((curry' F θ).app X y).1 f x = θ.app Y (x ⊗ₜ[R.obj Y] G.map f y) := rfl

noncomputable def uncurryApp (κ : G ⟶ ihomObj F N) (X : Cᵒᵖ) : (F ⊗ G).obj X ⟶ N.obj X :=
  ModuleCat.MonoidalCategory.tensorLift (fun (x : F.obj X) (y : G.obj X) => (κ.app X y).1 (𝟙 X) x)
    (fun x x' y => by simp)
    (fun r x y => by simp)
    (fun x y y' => by
      have h1 : κ.app X (y + y') = κ.app X y + κ.app X y' := (κ.app X).hom.map_add _ _
      simp only [h1]; rfl)
    (fun r x y => by
      have h1 : κ.app X (r • y) = r • κ.app X y := (κ.app X).hom.map_smul _ _
      simp only [h1]
      change R.map (𝟙 X) r • (κ.app X y).1 (𝟙 X) x = _
      rw [R.map_id]
      rfl)

lemma tensorObj_map_tmul' {X Y : Cᵒᵖ} (g : X ⟶ Y) (x : F.obj X) (y : G.obj X) :
    DFunLike.coe (α := (F.obj X ⊗ G.obj X :))
      (β := fun _ => (ModuleCat.restrictScalars (R.map g).hom).obj (F.obj Y ⊗ G.obj Y))
      (ModuleCat.Hom.hom (R := ↑(R.obj X)) ((F ⊗ G).map g)) (x ⊗ₜ[R.obj X] y) =
    F.map g x ⊗ₜ[R.obj Y] G.map g y := rfl

lemma uncurryApp_tmul (κ : G ⟶ ihomObj F N) (X : Cᵒᵖ) (x : F.obj X) (y : G.obj X) :
    DFunLike.coe (α := (F.obj X ⊗ G.obj X :)) (β := fun _ => N.obj X)
      (uncurryApp F κ X).hom (x ⊗ₜ[R.obj X] y) = (κ.app X y).1 (𝟙 X) x := by
  erw [ModuleCat.MonoidalCategory.tensorLift_tmul]

noncomputable def uncurry' (κ : G ⟶ ihomObj F N) : F ⊗ G ⟶ N where
  app X := uncurryApp F κ X
  naturality {X Y} g := ModuleCat.MonoidalCategory.tensor_ext (fun x y => by
    dsimp
    erw [tensorObj_map_tmul' F (G := G) g x y]
    erw [uncurryApp_tmul, uncurryApp_tmul]
    rw [naturality_apply κ g y]
    erw [ihomObj_map_val]
    erw [(κ.app X y).2 (𝟙 X) g x]
    exact congr_app _ (by simp) _)

lemma uncurry'_app_tmul (κ : G ⟶ ihomObj F N) {X : Cᵒᵖ} (x : F.obj X) (y : G.obj X) :
    DFunLike.coe (α := (F.obj X ⊗ G.obj X :)) (β := fun _ => N.obj X)
      ((uncurry' F κ).app X).hom (x ⊗ₜ[R.obj X] y) = (κ.app X y).1 (𝟙 X) x :=
  uncurryApp_tmul F κ X x y

lemma uncurry'_curry' (θ : F ⊗ G ⟶ N) : uncurry' F (curry' F θ) = θ := by
  ext X : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  erw [uncurry'_app_tmul]
  change θ.app X (x ⊗ₜ[R.obj X] G.map (𝟙 X) y) = θ.app X (x ⊗ₜ[R.obj X] y)
  rw [InternalHom.map_id_apply]

lemma curry'_uncurry' (κ : G ⟶ ihomObj F N) : curry' F (uncurry' F κ) = κ := by
  ext X y
  apply naturalFamilies_ext; intro Y f x
  rw [curry'_app_val]
  erw [uncurry'_app_tmul]
  rw [naturality_apply κ f y, ihomObj_map_val]
  exact congr_app _ (by simp) _

noncomputable def tensorIhomAdj : tensorLeft F ⊣ ihomFunctor F :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun G N =>
        { toFun := curry' F
          invFun := uncurry' F
          left_inv := uncurry'_curry' F
          right_inv := curry'_uncurry' F }
      homEquiv_naturality_left_symm := fun {G G' N} γ κ => by
        ext X : 1
        apply ModuleCat.MonoidalCategory.tensor_ext
        intro x y
        change (uncurry' F (γ ≫ κ)).app X (x ⊗ₜ[R.obj X] y) =
          (uncurry' F κ).app X ((F ◁ γ).app X (x ⊗ₜ[R.obj X] y))
        erw [uncurry'_app_tmul, uncurry'_app_tmul]
      homEquiv_naturality_right := fun {G N N'} θ ν => by
        ext X y
        apply naturalFamilies_ext; intro Y f x
        rfl }

noncomputable instance instMonoidalClosed :
    MonoidalClosed (PresheafOfModules.{u} (R ⋙ forget₂ _ _)) where
  closed F := { rightAdj := ihomFunctor F, adj := tensorIhomAdj F }

end closed

end PresheafOfModules


