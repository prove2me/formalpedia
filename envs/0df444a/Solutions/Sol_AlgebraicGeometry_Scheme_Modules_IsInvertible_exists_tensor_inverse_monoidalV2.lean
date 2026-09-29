-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_tensor_inverse_monoidalV2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/4af5d4b5-9442-5232-82a1-7460a077352b

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_PresheafOfModules_InternalHom
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse_monoidalV2

section LinkageInlined_5b3a613b

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v' u'

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits Opposite"

noncomputable section

namespace PresheafOfModules
p2m_export "PresheafOfModules" "sheafification sheafify presheaf sections pullback naturality_apply pushforward evaluation inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms map map_comp_apply IsLocallyInjective Hom toPresheaf unit free restriction pullbackComp mk homMk obj IsLocallySurjective InternalHom.map_id_apply InternalHom.naturality InternalHom.smul_app InternalHom.presheaf ihomObj uncurry' uncurry'_app_tmul"
p2m_open "PresheafOfModules"

namespace InternalHom
p2m_export "PresheafOfModules.InternalHom" "map_id_apply naturalFamilies naturalFamilies_ext naturality congr_app smul_app presheaf"
p2m_open "PresheafOfModules.InternalHom"

variable {C : Type u'} [Category.{v'} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (F N : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

private noncomputable def toPresheafHom (X : Cᵒᵖ) (φ : naturalFamilies F N X) :
    (presheafHom F.presheaf N.presheaf).obj X where
  app Y := AddCommGrpCat.ofHom (φ.1 Y.unop.hom.op).toAddMonoidHom
  naturality {Y Y'} k := by
    ext x
    change φ.1 Y'.unop.hom.op (F.map k.unop.left.op x) = N.map k.unop.left.op (φ.1 Y.unop.hom.op x)
    rw [φ.2 Y.unop.hom.op k.unop.left.op x]
    exact congr_app φ (by rw [← op_comp, Over.w]) _

variable {F N} in

private abbrev appAt {X : Cᵒᵖ} (s : (presheafHom F.presheaf N.presheaf).obj X) (Y : (Over X.unop)ᵒᵖ)
    (x : F.obj (Opposite.op Y.unop.left)) : N.obj (Opposite.op Y.unop.left) :=
  s.app Y x

@[local simp] private lemma appAt_toPresheafHom (X : Cᵒᵖ) (φ : naturalFamilies F N X) (Y : (Over X.unop)ᵒᵖ)
    (x : F.obj (Opposite.op Y.unop.left)) :
    appAt (toPresheafHom F N X φ) Y x = φ.1 Y.unop.hom.op x := rfl

private noncomputable def linearSub : Subfunctor (presheafHom F.presheaf N.presheaf) where
  obj X := { s | ∀ (Y : (Over X.unop)ᵒᵖ) (r : R.obj (Opposite.op Y.unop.left))
    (x : F.obj (Opposite.op Y.unop.left)), appAt s Y (r • x) = r • appAt s Y x }
  map h _ hs Y r x := hs (Opposite.op ((Over.map h.unop).obj Y.unop)) r x

private noncomputable def ofPresheafHom (X : Cᵒᵖ) (s : (linearSub F N).obj X) : naturalFamilies F N X :=
  ⟨fun Y f =>
    { toFun := fun x => appAt s.1 (Opposite.op (Over.mk f.unop)) x
      map_add' := fun x x' => (s.1.app _).hom.map_add _ _
      map_smul' := fun r x => s.2 (Opposite.op (Over.mk f.unop)) r x }, by
    intro Y Z f g x
    change N.map g (appAt s.1 (Opposite.op (Over.mk f.unop)) x) =
      appAt s.1 (Opposite.op (Over.mk (g.unop ≫ f.unop))) (F.map g x)
    have := s.1.naturality (Over.homMk g.unop rfl : Over.mk (g.unop ≫ f.unop) ⟶ Over.mk f.unop).op
    exact (ConcreteCategory.congr_hom this x).symm⟩

private lemma ofPresheafHom_app (X : Cᵒᵖ) (s : (linearSub F N).obj X) {Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : F.obj Y) :
    (ofPresheafHom F N X s).1 f x = appAt s.1 (Opposite.op (Over.mk f.unop)) x := rfl

private noncomputable def equivLinearSub (X : Cᵒᵖ) : naturalFamilies F N X ≃ (linearSub F N).obj X where
  toFun φ := ⟨toPresheafHom F N X φ, fun Y r x => (φ.1 Y.unop.hom.op).map_smul r x⟩
  invFun s := ofPresheafHom F N X s
  left_inv φ := by
    apply naturalFamilies_ext; intro Y f x; rfl
  right_inv s := by rfl

private noncomputable def isoLinearSub :
    InternalHom.presheaf F N ⋙ forget AddCommGrpCat ≅ (linearSub F N).toFunctor :=
  NatIso.ofComponents (fun X => (equivLinearSub F N X).toIso) (by intros; rfl)

variable {F N}

private lemma linearSub_local {J : GrothendieckTopology C}
    (hNsep : Presieve.IsSeparated J (N.presheaf ⋙ forget AddCommGrpCat))
    (X : Cᵒᵖ) (s : (presheafHom F.presheaf N.presheaf).obj X)
    (hs : (linearSub F N).sieveOfSection s ∈ J X.unop) : s ∈ (linearSub F N).obj X := by
  intro Y r x
  obtain ⟨Y⟩ := Y
  apply (hNsep _ (J.pullback_stable Y.hom hs)).ext
  intro W k hk

  have nat : ∀ x' : F.obj (Opposite.op Y.left),
      appAt s (Opposite.op (Over.mk (k ≫ Y.hom))) (F.map k.op x') =
        N.map k.op (appAt s (Opposite.op Y) x') := fun x' =>
    ConcreteCategory.congr_hom (s.naturality (Over.homMk k rfl : Over.mk (k ≫ Y.hom) ⟶ Y).op) x'

  have hlin : ∀ (ρ : R.obj (Opposite.op W)) (z : F.obj (Opposite.op W)),
      appAt s (Opposite.op (Over.mk (k ≫ Y.hom))) (ρ • z) =
        ρ • appAt s (Opposite.op (Over.mk (k ≫ Y.hom))) z := fun ρ z => by
    have h := hk (Opposite.op (Over.mk (𝟙 W))) ρ z
    have e := presheafHom_map_app_op_mk_id (F := F.presheaf) (G := N.presheaf) (k ≫ Y.hom) s
    dsimp only [appAt] at h ⊢
    erw [e] at h
    exact h
  change N.map k.op (appAt s (Opposite.op Y) (r • x)) = N.map k.op (r • appAt s (Opposite.op Y) x)
  rw [← nat, N.map_smul, ← nat, F.map_smul]
  exact hlin _ _

end InternalHom

end PresheafOfModules

end

namespace PresheafOfModules p2m_export "PresheafOfModules" "sheafification sheafify presheaf sections pullback naturality_apply pushforward evaluation inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms map map_comp_apply IsLocallyInjective Hom toPresheaf unit free restriction pullbackComp mk homMk obj IsLocallySurjective InternalHom.map_id_apply InternalHom.naturality InternalHom.smul_app InternalHom.presheaf ihomObj uncurry' uncurry'_app_tmul" end PresheafOfModules
p2m_open_scoped "PresheafOfModules" in

private theorem PresheafOfModules.isSheaf_ihomObj {C : Type u} [Category.{u} C]
    {R : Cᵒᵖ ⥤ CommRingCat.{u}} (F N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    {J : GrothendieckTopology C} (hN : Presheaf.IsSheaf J N.presheaf) :
    Presheaf.IsSheaf J (PresheafOfModules.ihomObj F N).presheaf := by
  change Presheaf.IsSheaf J (PresheafOfModules.InternalHom.presheaf F N)
  rw [Presheaf.isSheaf_iff_isSheaf_comp J _ (forget AddCommGrpCat), isSheaf_iff_isSheaf_of_type]
  refine Presieve.isSheaf_iso J (PresheafOfModules.InternalHom.isoLinearSub F N).symm ?_
  have hH : Presieve.IsSheaf J (presheafHom F.presheaf N.presheaf) :=
    (isSheaf_iff_isSheaf_of_type _ _).1 (hN.hom F.presheaf)
  have hNsep : Presieve.IsSeparated J (N.presheaf ⋙ forget AddCommGrpCat) :=
    ((isSheaf_iff_isSheaf_of_type _ _).1
      ((Presheaf.isSheaf_iff_isSheaf_comp J N.presheaf (forget AddCommGrpCat)).1 hN)).isSeparated
  rw [(PresheafOfModules.InternalHom.linearSub F N).isSheaf_iff hH]
  intro X s hs
  exact PresheafOfModules.InternalHom.linearSub_local hNsep X s hs

end LinkageInlined_5b3a613b

section LinkageInlined_23d4f55a

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits"

namespace PresheafOfModules
p2m_export "PresheafOfModules" "sheafification sheafify presheaf sections pullback naturality_apply pushforward evaluation inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms map map_comp_apply IsLocallyInjective Hom toPresheaf unit free restriction pullbackComp mk homMk obj IsLocallySurjective InternalHom.map_id_apply InternalHom.naturality InternalHom.smul_app InternalHom.presheaf ihomObj uncurry' uncurry'_app_tmul"
p2m_open "PresheafOfModules"

namespace InvertibleDual

p2m_open "Opposite PresheafOfModules.InternalHom P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse_monoidalV2.PresheafOfModules.InternalHom TensorProduct"

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (F : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))

private noncomputable abbrev dual : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat) :=
  ihomObj F (𝟙_ _)

private noncomputable abbrev ev : F ⊗ dual F ⟶ 𝟙_ _ := uncurry' F (𝟙 (dual F))

private structure TrivializationBelow (X₀ : Cᵒᵖ) where

  gen : ∀ {Y : Cᵒᵖ} (_ : X₀ ⟶ Y), F.obj Y
  compat : ∀ {Y Z : Cᵒᵖ} (f : X₀ ⟶ Y) (g : Y ⟶ Z), F.map g (gen f) = gen (f ≫ g)
  bij : ∀ {Y : Cᵒᵖ} (f : X₀ ⟶ Y), Function.Bijective (fun a : R.obj Y => a • gen f)

variable {F} {X₀ : Cᵒᵖ} (D : TrivializationBelow F X₀)

namespace TrivializationBelow

private noncomputable def restrictTo {Y : Cᵒᵖ} (f : X₀ ⟶ Y) : TrivializationBelow F Y where
  gen g := D.gen (f ≫ g)
  compat g g' := by rw [D.compat, Category.assoc]
  bij g := D.bij (f ≫ g)

private noncomputable def triv {Y : Cᵒᵖ} (f : X₀ ⟶ Y) : R.obj Y ≃ₗ[R.obj Y] F.obj Y :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton (R.obj Y) (F.obj Y) (D.gen f)) (D.bij f)

private noncomputable def coord {Y : Cᵒᵖ} (f : X₀ ⟶ Y) : F.obj Y →ₗ[R.obj Y] R.obj Y := (D.triv f).symm

private lemma coord_smul_gen {Y : Cᵒᵖ} (f : X₀ ⟶ Y) (x : F.obj Y) : D.coord f x • D.gen f = x :=
  (D.triv f).apply_symm_apply x

private lemma coord_gen_smul {Y : Cᵒᵖ} (f : X₀ ⟶ Y) (a : R.obj Y) : D.coord f (a • D.gen f) = a :=
  (D.triv f).symm_apply_apply a

@[local simp] private lemma coord_gen {Y : Cᵒᵖ} (f : X₀ ⟶ Y) : D.coord f (D.gen f) = 1 := by
  simpa using D.coord_gen_smul f 1

private lemma coord_map {Y Z : Cᵒᵖ} (f : X₀ ⟶ Y) (g : Y ⟶ Z) (x : F.obj Y) :
    D.coord (f ≫ g) (F.map g x) = R.map g (D.coord f x) := by
  conv_lhs => rw [← D.coord_smul_gen f x]
  rw [PresheafOfModules.map_smul, D.compat]
  exact D.coord_gen_smul (f ≫ g) _

private noncomputable def dualGen : (dual F).obj X₀ :=
  ⟨fun Y f => D.coord f, fun Y Z f g x => by
    change R.map g (D.coord f x) = D.coord (f ≫ g) (F.map g x)
    rw [D.coord_map]⟩

@[local simp] private lemma dualGen_app {Y : Cᵒᵖ} (f : X₀ ⟶ Y) (x : F.obj Y) :
    (D.dualGen).1 f x = D.coord f x := rfl

private lemma eq_smul_dualGen (φ : (dual F).obj X₀) : φ = φ.1 (𝟙 X₀) (D.gen (𝟙 X₀)) • D.dualGen := by
  apply naturalFamilies_ext
  intro Y f x
  rw [InternalHom.smul_app, dualGen_app]
  conv_lhs => rw [← D.coord_smul_gen f x, LinearMap.map_smul]
  have h := InternalHom.naturality φ (𝟙 X₀) f (D.gen (𝟙 X₀))
  rw [D.compat, Category.id_comp] at h
  rw [← h, smul_eq_mul, smul_eq_mul, mul_comm]
  rfl

private noncomputable def evInv : R.obj X₀ →ₗ[R.obj X₀] (F.obj X₀ ⊗[R.obj X₀] (dual F).obj X₀) :=
  LinearMap.toSpanSingleton _ _ (D.gen (𝟙 X₀) ⊗ₜ D.dualGen)

omit D in
private lemma ev_app_tmul (x : F.obj X₀) (φ : (dual F).obj X₀) :
    DFunLike.coe (α := (F.obj X₀ ⊗ (dual F).obj X₀ :)) (β := fun _ => (𝟙_ (PresheafOfModules.{u}
      (R ⋙ forget₂ CommRingCat RingCat))).obj X₀)
      ((ev F).app X₀).hom (x ⊗ₜ[R.obj X₀] φ) = φ.1 (𝟙 X₀) x :=
  uncurry'_app_tmul F (𝟙 (dual F)) x φ

private lemma ev_evInv (a : R.obj X₀) :
    DFunLike.coe (α := (F.obj X₀ ⊗ (dual F).obj X₀ :)) (β := fun _ => (𝟙_ (PresheafOfModules.{u}
      (R ⋙ forget₂ CommRingCat RingCat))).obj X₀)
      ((ev F).app X₀).hom (D.evInv a) = a := by
  change DFunLike.coe (α := (F.obj X₀ ⊗ (dual F).obj X₀ :)) (β := fun _ => (𝟙_ (PresheafOfModules.{u}
      (R ⋙ forget₂ CommRingCat RingCat))).obj X₀)
      ((ev F).app X₀).hom (a • (D.gen (𝟙 X₀) ⊗ₜ[R.obj X₀] D.dualGen)) = a
  rw [LinearMap.map_smul]
  erw [ev_app_tmul]
  rw [dualGen_app, coord_gen, smul_eq_mul, mul_one]

private lemma evInv_ev (z : (F.obj X₀ ⊗[R.obj X₀] (dual F).obj X₀)) :
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

private theorem ev_app_bijective (D : TrivializationBelow F X₀) : Function.Bijective ((ev F).app X₀) :=
  Function.bijective_iff_has_inverse.2 ⟨D.evInv, D.evInv_ev, D.ev_evInv⟩

end TrivializationBelow

variable (F) in

private theorem W_ev {J : GrothendieckTopology C} [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
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

end PresheafOfModules

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom Scheme.Opens.ι_appIso Scheme.Hom.image_preimage_eq_opensRange_inf Scheme IsSeparated Scheme.Modules Scheme.Opens Scheme.Opens.opensRange_ι Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.Modules.tensorIsoSheafify"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "forget ringCatSheaf Modules.pullback Hom mk Γ Opens.ι_appIso Hom.image_preimage_eq_opensRange_inf Modules.restrictFunctor restrictFunctor Modules.pullbackCongr Modules Opens homOfLE_ι grothendieckTopology Opens.opensRange_ι PresheafOfModules Modules.pullbackComp evaluation Modules.IsInvertible Modules.pullbackUnitIso Modules.sheafify Modules.tensorIsoSheafify"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "toPresheaf pushforward pullback presheaf Hom restrictFunctor restrictFunctorIsoPullback pullbackCongr isSheaf map_smul pullbackComp IsInvertible pullbackUnitIso tensor dual sheafify tensorIsoSheafify pullbackTensorUnitObjIso"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

open TopologicalSpace Opposite PresheafOfModules.InvertibleDual

variable {X : Scheme.{u}}

private noncomputable def trivializationOfLE_23d4f55a {U V : X.Opens} (h : V ≤ U) (L : X.Modules)
    (e : (Modules.pullback U.ι).obj L ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) :
    (Modules.pullback V.ι).obj L ≅ SheafOfModules.unit (V : Scheme.{u}).ringCatSheaf :=
  (Modules.pullbackCongr (X.homOfLE_ι h).symm).app L ≪≫
    ((Modules.pullbackComp (X.homOfLE h) U.ι).symm).app L ≪≫
    (Modules.pullback (X.homOfLE h)).mapIso e ≪≫
    Scheme.Modules.pullbackUnitIso (X.homOfLE h)

private noncomputable def dualSheaf (L : X.Modules) : X.Modules where
  val := PresheafOfModules.ihomObj L.val (𝟙_ X.PresheafOfModules)
  isSheaf := PresheafOfModules.isSheaf_ihomObj L.val _ (SheafOfModules.unit X.ringCatSheaf).isSheaf

variable (U : X.Opens)

private noncomputable def restrictRingCatSheafHom : (U : Scheme.{u}).ringCatSheaf ⟶
    (U.ι.opensFunctor.sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology (U : Scheme.{u})) (Opens.grothendieckTopology X)).obj
        X.ringCatSheaf :=
  ⟨𝟙 _⟩

private noncomputable def restrictFunctor' : X.Modules ⥤ (U : Scheme.{u}).Modules :=
  SheafOfModules.pushforward (restrictRingCatSheafHom U)

private lemma restrictFunctor'_eq : restrictFunctor' U = Modules.restrictFunctor U.ι := by
  dsimp only [restrictFunctor', Modules.restrictFunctor, restrictRingCatSheafHom]
  congr 2
  ext V : 2
  change 𝟙 _ = (forget₂ CommRingCat RingCat).map (U.ι.appIso V.unop).inv
  rw [Scheme.Opens.ι_appIso]
  rfl

private noncomputable def restrictFunctor'IsoPullback : restrictFunctor' U ≅ Modules.pullback U.ι :=
  eqToIso (restrictFunctor'_eq U) ≪≫ restrictFunctorIsoPullback U.ι

variable {U} (L : X.Modules)

private lemma image_preimage_of_le {V : X.Opens} (h : V ≤ U) : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_eq_right.mpr h

section

variable (e : (restrictFunctor' U).obj L ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)

private noncomputable def gen₀ (W : (U : Scheme.{u}).Opens) : L.val.obj (op (U.ι ''ᵁ W)) :=
  (e.inv.val.app (op W)).hom (1 : Γ(U, W))

private lemma gen₀_spec (W : (U : Scheme.{u}).Opens) (b : Γ(X, U.ι ''ᵁ W)) :
    (e.inv.val.app (op W)).hom b = b • gen₀ L e W := by
  have := (e.inv.val.app (op W)).hom.map_smul b (1 : Γ(U, W))
  rw [smul_eq_mul, mul_one] at this
  exact this

private lemma gen₀_bijective (W : (U : Scheme.{u}).Opens) :
    Function.Bijective (fun b : Γ(X, U.ι ''ᵁ W) => b • gen₀ L e W) := by
  have h : Function.Bijective ((e.inv.val.app (op W)).hom) := by
    refine Function.bijective_iff_has_inverse.2 ⟨(e.hom.val.app (op W)).hom, fun b => ?_, fun m => ?_⟩
    · exact congr($(e.inv_hom_id).val.app (op W) |>.hom b)
    · exact congr($(e.hom_inv_id).val.app (op W) |>.hom m)
  exact (funext (gen₀_spec L e W) ▸ h :)

private lemma gen₀_map {W W' : (U : Scheme.{u}).Opens} (i : W' ⟶ W) :
    L.val.map (U.ι.opensFunctor.map i).op (gen₀ L e W) = gen₀ L e W' := by
  have := PresheafOfModules.naturality_apply e.inv.val i.op (1 : Γ(U, W))

  rw [show ((SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf).val.map i.op) (1 : Γ(U, W)) =
    (1 : Γ(U, W')) from ((U : Scheme.{u}).presheaf.map i.op).hom.map_one] at this
  exact this.symm

omit e in

private lemma bijective_smul_map_eqToHom {A B : X.Opens} (q : A = B) (t : L.val.obj (op A))
    (h : Function.Bijective (fun b : Γ(X, A) => b • t)) :
    Function.Bijective (fun a : Γ(X, B) => a • L.val.map (eqToHom q.symm : B ⟶ A).op t) := by
  subst q
  have e1 : L.val.map (eqToHom (rfl : A = A) : A ⟶ A).op t = t := by
    rw [eqToHom_refl, op_id]
    exact PresheafOfModules.InternalHom.map_id_apply (R := X.sheaf.obj) L.val _ _
  simpa only [e1] using h

private noncomputable def trivializationBelow : TrivializationBelow L.val (op U) where
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

private def trivSieve (V : X.Opens) : Sieve V where
  arrows W _ := Nonempty (TrivializationBelow L.val (op W))
  downward_closed {W W'} f hf g := by
    obtain ⟨D⟩ := hf
    exact ⟨D.restrictTo g.op⟩

private lemma trivSieve_mem (hL : Scheme.Modules.IsInvertible L) (V : X.Opens) :
    trivSieve L V ∈ Opens.grothendieckTopology X V := by
  intro x hx
  obtain ⟨U, hxU, ⟨eU⟩⟩ := hL.1 x
  refine ⟨V ⊓ U, homOfLE inf_le_left, ?_, ⟨hx, hxU⟩⟩

  let e' : (Modules.pullback (V ⊓ U).ι).obj L ≅ SheafOfModules.unit ((V ⊓ U : X.Opens) :
      Scheme.{u}).ringCatSheaf := trivializationOfLE_23d4f55a inf_le_right L eU
  exact ⟨trivializationBelow L ((restrictFunctor'IsoPullback (V ⊓ U)).app L ≪≫ e')⟩

private local instance isIso_sheafify_map_ev (L : X.Modules) [Fact (Scheme.Modules.IsInvertible L)] :
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

private noncomputable def tensorDualSheafIso (L : X.Modules) [Fact (Scheme.Modules.IsInvertible L)] :
    L ⊗ dualSheaf L ≅ 𝟙_ X.Modules :=
  (Scheme.Modules.tensorIsoSheafify L (dualSheaf L)).symm ≪≫
    asIso ((Modules.sheafify X).map (ev (R := X.sheaf.obj) L.val)) ≪≫
    SheafOfModules.sheafifyUnitIso X.sheaf.obj X.ringCatSheaf.property

private theorem isInvertible_dualSheaf (L : X.Modules) [Fact (Scheme.Modules.IsInvertible L)] :
    Scheme.Modules.IsInvertible (dualSheaf L) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hxU, ⟨eU⟩⟩ := (Fact.out : Scheme.Modules.IsInvertible L).1 x
  refine ⟨U, hxU, ⟨?_⟩⟩
  exact (λ_ _).symm ≪≫ (eU.symm ⊗ᵢ Iso.refl _) ≪≫
    Functor.Monoidal.μIso (Modules.pullback U.ι) L (dualSheaf L) ≪≫
    (Modules.pullback U.ι).mapIso (tensorDualSheafIso L) ≪≫
    pullbackTensorUnitObjIso U.ι

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Scheme.Hom Scheme.Opens.ι_appIso Scheme.Hom.image_preimage_eq_opensRange_inf Scheme IsSeparated Scheme.Modules Scheme.Opens Scheme.Opens.opensRange_ι Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.Modules.tensorIsoSheafify" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "forget ringCatSheaf Modules.pullback Hom mk Γ Opens.ι_appIso Hom.image_preimage_eq_opensRange_inf Modules.restrictFunctor restrictFunctor Modules.pullbackCongr Modules Opens homOfLE_ι grothendieckTopology Opens.opensRange_ι PresheafOfModules Modules.pullbackComp evaluation Modules.IsInvertible Modules.pullbackUnitIso Modules.sheafify Modules.tensorIsoSheafify" namespace Modules p2m_export "AlgebraicGeometry.Scheme.Modules" "toPresheaf pushforward pullback presheaf Hom restrictFunctor restrictFunctorIsoPullback pullbackCongr isSheaf map_smul pullbackComp IsInvertible pullbackUnitIso tensor dual sheafify tensorIsoSheafify pullbackTensorUnitObjIso" namespace IsInvertible p2m_export "AlgebraicGeometry.Scheme.Modules.IsInvertible" "pullback mk" end AlgebraicGeometry.Scheme.Modules.IsInvertible
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.IsInvertible" in
open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse_monoidalV2.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse_monoidalV2.AlgebraicGeometry.Scheme.Modules in

private theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_tensor_inverse {X : AlgebraicGeometry.Scheme.{u}} {L : X.Modules}
    (hL : AlgebraicGeometry.Scheme.Modules.IsInvertible L) :
    ∃ M : X.Modules, AlgebraicGeometry.Scheme.Modules.IsInvertible M ∧
      Nonempty (L ⊗ M ≅ 𝟙_ X.Modules) :=
  haveI : Fact (Scheme.Modules.IsInvertible L) := ⟨hL⟩
  ⟨dualSheaf L, isInvertible_dualSheaf L, ⟨tensorDualSheafIso L⟩⟩

end LinkageInlined_23d4f55a

universe u

open CategoryTheory _root_.CategoryTheory.MonoidalCategory in
theorem solution
    {X : AlgebraicGeometry.Scheme.{u}} {L : X.Modules}
    (hL : AlgebraicGeometry.Scheme.Modules.IsInvertible L) :
    ∃ M : X.Modules, AlgebraicGeometry.Scheme.Modules.IsInvertible M ∧
      Nonempty (L ⊗ M ≅ 𝟙_ X.Modules) :=
  AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_tensor_inverse hL

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse_monoidalV2
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse_monoidalV2 (solution)
