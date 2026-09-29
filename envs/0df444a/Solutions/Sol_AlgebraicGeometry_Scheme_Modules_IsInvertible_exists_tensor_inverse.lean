-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_tensor_inverse
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/444b9d6c-a387-552a-a744-c899f77e09cb

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_PresheafOfModules_InternalHom
import Theorems.Thm_PresheafOfModules_isSheaf_ihomObj
import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_PresheafOfModules_PullbackMonoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits"

namespace PresheafOfModules
p2m_export "PresheafOfModules" "sheafification sheafify presheaf sections pullback naturality_apply pushforward evaluation inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms map map_comp_apply IsLocallyInjective Hom toPresheaf unit free restriction pullbackComp obj IsLocallySurjective InternalHom.map_id_apply InternalHom.naturality InternalHom.smul_app ihomObj uncurry' uncurry'_app_tmul isSheaf_ihomObj"
p2m_open "PresheafOfModules"

namespace InvertibleDual

p2m_open "Opposite PresheafOfModules.InternalHom TensorProduct"

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (F : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))

noncomputable abbrev dual : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat) :=
  ihomObj F (𝟙_ _)

noncomputable abbrev ev : F ⊗ dual F ⟶ 𝟙_ _ := uncurry' F (𝟙 (dual F))

structure TrivializationBelow (X₀ : Cᵒᵖ) where

  gen : ∀ {Y : Cᵒᵖ} (_ : X₀ ⟶ Y), F.obj Y
  compat : ∀ {Y Z : Cᵒᵖ} (f : X₀ ⟶ Y) (g : Y ⟶ Z), F.map g (gen f) = gen (f ≫ g)
  bij : ∀ {Y : Cᵒᵖ} (f : X₀ ⟶ Y), Function.Bijective (fun a : R.obj Y => a • gen f)

variable {F} {X₀ : Cᵒᵖ} (D : TrivializationBelow F X₀)

namespace TrivializationBelow

noncomputable def restrictTo {Y : Cᵒᵖ} (f : X₀ ⟶ Y) : TrivializationBelow F Y where
  gen g := D.gen (f ≫ g)
  compat g g' := by rw [D.compat, Category.assoc]
  bij g := D.bij (f ≫ g)

noncomputable def triv {Y : Cᵒᵖ} (f : X₀ ⟶ Y) : R.obj Y ≃ₗ[R.obj Y] F.obj Y :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton (R.obj Y) (F.obj Y) (D.gen f)) (D.bij f)

noncomputable def coord {Y : Cᵒᵖ} (f : X₀ ⟶ Y) : F.obj Y →ₗ[R.obj Y] R.obj Y := (D.triv f).symm

lemma coord_smul_gen {Y : Cᵒᵖ} (f : X₀ ⟶ Y) (x : F.obj Y) : D.coord f x • D.gen f = x :=
  (D.triv f).apply_symm_apply x

lemma coord_gen_smul {Y : Cᵒᵖ} (f : X₀ ⟶ Y) (a : R.obj Y) : D.coord f (a • D.gen f) = a :=
  (D.triv f).symm_apply_apply a

@[scoped simp] lemma coord_gen {Y : Cᵒᵖ} (f : X₀ ⟶ Y) : D.coord f (D.gen f) = 1 := by
  simpa using D.coord_gen_smul f 1

lemma coord_map {Y Z : Cᵒᵖ} (f : X₀ ⟶ Y) (g : Y ⟶ Z) (x : F.obj Y) :
    D.coord (f ≫ g) (F.map g x) = R.map g (D.coord f x) := by
  conv_lhs => rw [← D.coord_smul_gen f x]
  rw [PresheafOfModules.map_smul, D.compat]
  exact D.coord_gen_smul (f ≫ g) _

noncomputable def dualGen : (dual F).obj X₀ :=
  ⟨fun Y f => D.coord f, fun Y Z f g x => by
    change R.map g (D.coord f x) = D.coord (f ≫ g) (F.map g x)
    rw [D.coord_map]⟩

@[scoped simp] lemma dualGen_app {Y : Cᵒᵖ} (f : X₀ ⟶ Y) (x : F.obj Y) :
    (D.dualGen).1 f x = D.coord f x := rfl

lemma eq_smul_dualGen (φ : (dual F).obj X₀) : φ = φ.1 (𝟙 X₀) (D.gen (𝟙 X₀)) • D.dualGen := by
  apply naturalFamilies_ext
  intro Y f x
  rw [InternalHom.smul_app, dualGen_app]
  conv_lhs => rw [← D.coord_smul_gen f x, LinearMap.map_smul]
  have h := InternalHom.naturality φ (𝟙 X₀) f (D.gen (𝟙 X₀))
  rw [D.compat, Category.id_comp] at h
  rw [← h, smul_eq_mul, smul_eq_mul, mul_comm]
  rfl

noncomputable def evInv : R.obj X₀ →ₗ[R.obj X₀] (F.obj X₀ ⊗[R.obj X₀] (dual F).obj X₀) :=
  LinearMap.toSpanSingleton _ _ (D.gen (𝟙 X₀) ⊗ₜ D.dualGen)

omit D in
lemma ev_app_tmul (x : F.obj X₀) (φ : (dual F).obj X₀) :
    DFunLike.coe (α := (F.obj X₀ ⊗ (dual F).obj X₀ :)) (β := fun _ => (𝟙_ (PresheafOfModules.{u}
      (R ⋙ forget₂ CommRingCat RingCat))).obj X₀)
      ((ev F).app X₀).hom (x ⊗ₜ[R.obj X₀] φ) = φ.1 (𝟙 X₀) x :=
  uncurry'_app_tmul F (𝟙 (dual F)) x φ

lemma ev_evInv (a : R.obj X₀) :
    DFunLike.coe (α := (F.obj X₀ ⊗ (dual F).obj X₀ :)) (β := fun _ => (𝟙_ (PresheafOfModules.{u}
      (R ⋙ forget₂ CommRingCat RingCat))).obj X₀)
      ((ev F).app X₀).hom (D.evInv a) = a := by
  change DFunLike.coe (α := (F.obj X₀ ⊗ (dual F).obj X₀ :)) (β := fun _ => (𝟙_ (PresheafOfModules.{u}
      (R ⋙ forget₂ CommRingCat RingCat))).obj X₀)
      ((ev F).app X₀).hom (a • (D.gen (𝟙 X₀) ⊗ₜ[R.obj X₀] D.dualGen)) = a
  rw [LinearMap.map_smul]
  erw [ev_app_tmul]
  rw [dualGen_app, coord_gen, smul_eq_mul, mul_one]

lemma evInv_ev (z : (F.obj X₀ ⊗[R.obj X₀] (dual F).obj X₀)) :
    D.evInv (DFunLike.coe (α := (F.obj X₀ ⊗ (dual F).obj X₀ :)) (β := fun _ =>
      (𝟙_ (PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))).obj X₀)
        ((ev F).app X₀).hom z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  | tmul x φ =>
    erw [ev_app_tmul]
    set d : R.obj X₀ := φ.1 (𝟙 X₀) (D.gen (𝟙 X₀)) with hd
    have hx : x = D.coord (𝟙 X₀) x • D.gen (𝟙 X₀) := (D.coord_smul_gen _ x).symm
    have hφ : φ = d • D.dualGen := D.eq_smul_dualGen φ
    have h1 : φ.1 (𝟙 X₀) x = D.coord (𝟙 X₀) x * d := by
      conv_lhs => rw [hx]
      rw [LinearMap.map_smul, smul_eq_mul]
    rw [h1]
    conv_rhs => rw [hx, hφ, TensorProduct.smul_tmul_smul]
    rfl

theorem ev_app_bijective (D : TrivializationBelow F X₀) : Function.Bijective ((ev F).app X₀) :=
  Function.bijective_iff_has_inverse.2 ⟨D.evInv, D.evInv_ev, D.ev_evInv⟩

end TrivializationBelow
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse.PresheafOfModules.InvertibleDual.TrivializationBelow"

variable (F) in

theorem W_ev {J : GrothendieckTopology C} [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (hloc : ∀ (U : C), ∃ (S : Sieve U), S ∈ J U ∧
      ∀ ⦃V : C⦄ (f : V ⟶ U), S f → Nonempty (TrivializationBelow F (op V))) :
    J.W ((toPresheaf _).map (ev F)) := by
  have hsurj : Presheaf.IsLocallySurjective J ((toPresheaf _).map (ev F)) := by
    constructor
    intro U s
    obtain ⟨S, hS, hS'⟩ := hloc U
    refine J.superset_covering ?_ hS
    intro V i hi
    obtain ⟨D⟩ := hS' i hi
    obtain ⟨t, ht⟩ := D.ev_app_bijective.2 (((𝟙_ (PresheafOfModules.{u}
      (R ⋙ forget₂ CommRingCat RingCat))).presheaf.map i.op) s)
    exact ⟨t, ht⟩
  have hinj : Presheaf.IsLocallyInjective J ((toPresheaf _).map (ev F)) := by
    constructor
    intro U x y h
    obtain ⟨S, hS, hS'⟩ := hloc U.unop
    refine J.superset_covering ?_ hS
    intro V i hi
    obtain ⟨D⟩ := hS' i hi
    have nx := ConcreteCategory.congr_hom (((toPresheaf _).map (ev F)).naturality i.op) x
    have ny := ConcreteCategory.congr_hom (((toPresheaf _).map (ev F)).naturality i.op) y
    simp only [ConcreteCategory.comp_apply] at nx ny
    change (F ⊗ dual F).presheaf.map i.op x = (F ⊗ dual F).presheaf.map i.op y
    apply D.ev_app_bijective.1
    change ((toPresheaf _).map (ev F)).app _ ((F ⊗ dual F).presheaf.map i.op x) =
      ((toPresheaf _).map (ev F)).app _ ((F ⊗ dual F).presheaf.map i.op y)
    erw [nx, ny, h]
  exact J.W_of_isLocallyBijective _

end InvertibleDual
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse.PresheafOfModules.InvertibleDual.TrivializationBelow P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse.PresheafOfModules.InvertibleDual"

end PresheafOfModules
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse.PresheafOfModules.InvertibleDual.TrivializationBelow P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse.PresheafOfModules.InvertibleDual P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse.PresheafOfModules"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom Scheme.Opens.ι_appIso Scheme.Hom.image_preimage_eq_opensRange_inf Scheme Scheme.Modules Scheme.Opens Scheme.Opens.opensRange_ι Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.Modules.tensorIsoSheafify"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "ringCatSheaf Modules.pullback Hom Γ Opens.ι_appIso Hom.image_preimage_eq_opensRange_inf Modules.restrictFunctor restrictFunctor Modules.pullbackCongr Modules Opens homOfLE_ι grothendieckTopology Opens.opensRange_ι PresheafOfModules Modules.pullbackComp evaluation Modules.IsInvertible Modules.pullbackUnitIso Modules.sheafify Modules.tensorIsoSheafify"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "toPresheaf pushforward pullback presheaf Hom restrictFunctor restrictFunctorIsoPullback pullbackCongr isSheaf map_smul pullbackComp IsInvertible pullbackUnitIso tensor dual sheafify tensorIsoSheafify pullbackTensorUnitObjIso"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

open TopologicalSpace Opposite PresheafOfModules.InvertibleDual

variable {X : Scheme.{u}}

noncomputable def trivializationOfLE {U V : X.Opens} (h : V ≤ U) (L : X.Modules)
    (e : (Modules.pullback U.ι).obj L ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) :
    (Modules.pullback V.ι).obj L ≅ SheafOfModules.unit (V : Scheme.{u}).ringCatSheaf :=
  (Modules.pullbackCongr (X.homOfLE_ι h).symm).app L ≪≫
    ((Modules.pullbackComp (X.homOfLE h) U.ι).symm).app L ≪≫
    (Modules.pullback (X.homOfLE h)).mapIso e ≪≫
    Scheme.Modules.pullbackUnitIso (X.homOfLE h)

noncomputable def dualSheaf (L : X.Modules) : X.Modules where
  val := PresheafOfModules.ihomObj L.val (𝟙_ X.PresheafOfModules)
  isSheaf := PresheafOfModules.isSheaf_ihomObj L.val _ (SheafOfModules.unit X.ringCatSheaf).isSheaf

variable (U : X.Opens)

noncomputable def restrictRingCatSheafHom : (U : Scheme.{u}).ringCatSheaf ⟶
    (U.ι.opensFunctor.sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology (U : Scheme.{u})) (Opens.grothendieckTopology X)).obj
        X.ringCatSheaf :=
  ⟨𝟙 _⟩

noncomputable def restrictFunctor' : X.Modules ⥤ (U : Scheme.{u}).Modules :=
  SheafOfModules.pushforward (restrictRingCatSheafHom U)

lemma restrictFunctor'_eq : restrictFunctor' U = Modules.restrictFunctor U.ι := by
  dsimp only [restrictFunctor', Modules.restrictFunctor, restrictRingCatSheafHom]
  congr 2
  ext V : 2
  change 𝟙 _ = (forget₂ CommRingCat RingCat).map (U.ι.appIso V.unop).inv
  rw [Scheme.Opens.ι_appIso]
  rfl

noncomputable def restrictFunctor'IsoPullback : restrictFunctor' U ≅ Modules.pullback U.ι :=
  eqToIso (restrictFunctor'_eq U) ≪≫ restrictFunctorIsoPullback U.ι

variable {U} (L : X.Modules)

lemma image_preimage_of_le {V : X.Opens} (h : V ≤ U) : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_eq_right.mpr h

section

variable (e : (restrictFunctor' U).obj L ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)

noncomputable def gen₀ (W : (U : Scheme.{u}).Opens) : L.val.obj (op (U.ι ''ᵁ W)) :=
  (e.inv.val.app (op W)).hom (1 : Γ(U, W))

lemma gen₀_spec (W : (U : Scheme.{u}).Opens) (b : Γ(X, U.ι ''ᵁ W)) :
    (e.inv.val.app (op W)).hom b = b • gen₀ L e W := by
  have := (e.inv.val.app (op W)).hom.map_smul b (1 : Γ(U, W))
  rw [smul_eq_mul, mul_one] at this
  exact this

lemma gen₀_bijective (W : (U : Scheme.{u}).Opens) :
    Function.Bijective (fun b : Γ(X, U.ι ''ᵁ W) => b • gen₀ L e W) := by
  have h : Function.Bijective ((e.inv.val.app (op W)).hom) := by
    refine Function.bijective_iff_has_inverse.2 ⟨(e.hom.val.app (op W)).hom, fun b => ?_, fun m => ?_⟩
    · exact congr($(e.inv_hom_id).val.app (op W) |>.hom b)
    · exact congr($(e.hom_inv_id).val.app (op W) |>.hom m)
  exact (funext (gen₀_spec L e W) ▸ h :)

lemma gen₀_map {W W' : (U : Scheme.{u}).Opens} (i : W' ⟶ W) :
    L.val.map (U.ι.opensFunctor.map i).op (gen₀ L e W) = gen₀ L e W' := by
  have := PresheafOfModules.naturality_apply e.inv.val i.op (1 : Γ(U, W))

  rw [show ((SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf).val.map i.op) (1 : Γ(U, W)) =
    (1 : Γ(U, W')) from ((U : Scheme.{u}).presheaf.map i.op).hom.map_one] at this
  exact this.symm

omit e in

lemma bijective_smul_map_eqToHom {A B : X.Opens} (q : A = B) (t : L.val.obj (op A))
    (h : Function.Bijective (fun b : Γ(X, A) => b • t)) :
    Function.Bijective (fun a : Γ(X, B) => a • L.val.map (eqToHom q.symm : B ⟶ A).op t) := by
  subst q
  have e1 : L.val.map (eqToHom (rfl : A = A) : A ⟶ A).op t = t := by
    rw [eqToHom_refl, op_id]
    exact PresheafOfModules.InternalHom.map_id_apply (R := X.sheaf.obj) L.val _ _
  simpa only [e1] using h

noncomputable def trivializationBelow : TrivializationBelow L.val (op U) where
  gen {Y} f := L.val.map (eqToHom (image_preimage_of_le (U := U) f.unop.le).symm :
      Y.unop ⟶ U.ι ''ᵁ (U.ι ⁻¹ᵁ Y.unop)).op (gen₀ L e (U.ι ⁻¹ᵁ Y.unop))
  compat {Y Z} f g := by
    have hle : U.ι ⁻¹ᵁ Z.unop ≤ U.ι ⁻¹ᵁ Y.unop := fun x hx => g.unop.le hx
    dsimp only
    rw [← gen₀_map L e (homOfLE hle)]
    erw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply]
    exact congrFun (congrArg
      (fun φ : (op (U.ι ''ᵁ (U.ι ⁻¹ᵁ Y.unop)) ⟶ Z) =>
        ((L.val.map φ).hom : L.val.obj (op (U.ι ''ᵁ (U.ι ⁻¹ᵁ Y.unop))) → L.val.obj Z))
      (Subsingleton.elim _ _)) _
  bij {Y} f := bijective_smul_map_eqToHom L (image_preimage_of_le (U := U) f.unop.le) _
    (gen₀_bijective L e _)

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse.PresheafOfModules.InvertibleDual.TrivializationBelow P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse.PresheafOfModules.InvertibleDual P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse.PresheafOfModules"

def trivSieve (V : X.Opens) : Sieve V where
  arrows W _ := Nonempty (TrivializationBelow L.val (op W))
  downward_closed {W W'} f hf g := by
    obtain ⟨D⟩ := hf
    exact ⟨D.restrictTo g.op⟩

lemma trivSieve_mem (hL : Scheme.Modules.IsInvertible L) (V : X.Opens) :
    trivSieve L V ∈ Opens.grothendieckTopology X V := by
  intro x hx
  obtain ⟨U, hxU, ⟨eU⟩⟩ := hL.1 x
  refine ⟨V ⊓ U, homOfLE inf_le_left, ?_, ⟨hx, hxU⟩⟩

  let e' : (Modules.pullback (V ⊓ U).ι).obj L ≅ SheafOfModules.unit ((V ⊓ U : X.Opens) :
      Scheme.{u}).ringCatSheaf := trivializationOfLE inf_le_right L eU
  exact ⟨trivializationBelow L ((restrictFunctor'IsoPullback (V ⊓ U)).app L ≪≫ e')⟩

scoped instance isIso_sheafify_map_ev (L : X.Modules) [Fact (Scheme.Modules.IsInvertible L)] :
    IsIso ((Modules.sheafify X).map (ev (R := X.sheaf.obj) L.val)) := by
  have hW : (Opens.grothendieckTopology X).W ((PresheafOfModules.toPresheaf _).map
      (ev (R := X.sheaf.obj) L.val)) :=
    W_ev (R := X.sheaf.obj) L.val (fun V => ⟨trivSieve L V, trivSieve_mem L Fact.out V,
      fun W i hi => hi⟩)
  have h : ((MorphismProperty.isomorphisms _).inverseImage
      (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)))
      (ev (R := X.sheaf.obj) L.val) := by
    rw [← PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (J := Opens.grothendieckTopology X) (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)]
    exact hW
  exact h

noncomputable def tensorDualSheafIso (L : X.Modules) [Fact (Scheme.Modules.IsInvertible L)] :
    L ⊗ dualSheaf L ≅ 𝟙_ X.Modules :=
  (Scheme.Modules.tensorIsoSheafify L (dualSheaf L)).symm ≪≫
    asIso ((Modules.sheafify X).map (ev (R := X.sheaf.obj) L.val)) ≪≫
    SheafOfModules.sheafifyUnitIso X.sheaf.obj X.ringCatSheaf.property

theorem isInvertible_dualSheaf (L : X.Modules) [Fact (Scheme.Modules.IsInvertible L)] :
    Scheme.Modules.IsInvertible (dualSheaf L) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hxU, ⟨eU⟩⟩ := (Fact.out : Scheme.Modules.IsInvertible L).1 x
  refine ⟨U, hxU, ⟨?_⟩⟩
  exact (λ_ _).symm ≪≫ (eU.symm ⊗ᵢ Iso.refl _) ≪≫
    Functor.Monoidal.μIso (Modules.pullback U.ι) L (dualSheaf L) ≪≫
    (Modules.pullback U.ι).mapIso (tensorDualSheafIso L) ≪≫
    pullbackTensorUnitObjIso U.ι

end AlgebraicGeometry.Scheme.Modules
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse.PresheafOfModules.InvertibleDual.TrivializationBelow P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse.PresheafOfModules.InvertibleDual P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse.PresheafOfModules P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse.AlgebraicGeometry.Scheme.Modules"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse.PresheafOfModules.InvertibleDual.TrivializationBelow P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse.PresheafOfModules.InvertibleDual P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse.PresheafOfModules P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse.AlgebraicGeometry.Scheme"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse.PresheafOfModules.InvertibleDual.TrivializationBelow P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse.PresheafOfModules.InvertibleDual P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse.PresheafOfModules P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse.AlgebraicGeometry"

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse.AlgebraicGeometry.Scheme.Modules in

theorem solution {X : AlgebraicGeometry.Scheme.{u}} {L : X.Modules}
    (hL : AlgebraicGeometry.Scheme.Modules.IsInvertible L) :
    ∃ M : X.Modules, AlgebraicGeometry.Scheme.Modules.IsInvertible M ∧
      Nonempty (L ⊗ M ≅ 𝟙_ X.Modules) :=
  haveI : Fact (Scheme.Modules.IsInvertible L) := ⟨hL⟩
  ⟨dualSheaf L, isInvertible_dualSheaf L, ⟨tensorDualSheafIso L⟩⟩

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse (solution)
