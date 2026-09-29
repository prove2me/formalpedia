-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.CechTrivialisation.comap_transition
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/068a6ecb-124e-5f26-a3a0-bb9cd27fd27b

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_hom_app_comp_pullbackUnitIso_hom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_comap_transition

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_comap_transition.AlgebraicGeometry Opposite TopologicalSpace"

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.resLE_comp_ι morphismRestrict_ι Scheme.Modules.pullback Scheme.Hom Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Scheme Scheme.Modules.Hom.id_app Scheme.Modules.Hom.app Scheme.Hom.resLE_map Scheme.Hom.appTop Scheme.Modules Scheme.Hom.resLE_app_top IsAffineHom Scheme.Modules.CechTrivialisation Scheme.Modules.homEquiv_symm_app_pullbackLocalSection Scheme.Modules.pullbackComp_hom_app_comp_pullbackUnitIso_hom"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.resLE_comp_ι ringCatSheaf Modules.pullback Hom.id_app Hom Γ Modules.Hom.comp_app Hom.app Modules.Hom topIso Modules.Hom.id_app Modules.Hom.app Hom.resLE_map Hom.appTop Hom.comp_app Modules Opens homOfLE_ι Hom.resLE_app_top restrict PresheafOfModules OrderedAffineCover Modules.CechTrivialisation Modules.homEquiv_symm_app_pullbackLocalSection Modules.pullbackComp_hom_app_comp_pullbackUnitIso_hom"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "pullback presheaf Hom.comp_app Hom pseudofunctor_associativity Hom.id_app Hom.app pullbackCongr pullbackPushforwardAdjunction restrict map_smul pullbackComp pullbackUnitIso unitAutSection CechTrivialisation CechTrivialisation.comap pullbackLocalSection pullbackLocalSection_app homEquiv_symm_app_pullbackLocalSection pullbackComp_hom_app_comp_pullbackUnitIso_hom"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {Y : Scheme.{u}}

noncomputable def uapp (W : Y.Opens)
    (e : SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf ≅ SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)
    (x : (W : Scheme.{u}).presheaf.obj (op ⊤)) : (W : Scheme.{u}).presheaf.obj (op ⊤) :=
  (e.hom.val.app (op ⊤)).hom x

theorem unitAutSection_eq (W : Y.Opens)
    (e : SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf ≅ SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf) :
    unitAutSection W e = W.topIso.hom.hom (uapp W e 1) := rfl

theorem uapp_mul (W : Y.Opens)
    (e : SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf ≅ SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)
    (x y : (W : Scheme.{u}).presheaf.obj (op ⊤)) : uapp W e (x * y) = x * uapp W e y :=
  ((e.hom.val.app (op ⊤)).hom).map_smul (show ((W : Scheme.{u}).ringCatSheaf.val.obj (op ⊤)) from x) y

theorem uapp_trans (W : Y.Opens)
    (e e' : SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf ≅ SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)
    (x : (W : Scheme.{u}).presheaf.obj (op ⊤)) : uapp W (e ≪≫ e') x = uapp W e' (uapp W e x) := by
  simp only [uapp, Iso.trans_hom, SheafOfModules.comp_val, PresheafOfModules.comp_app]
  rfl

theorem uapp_refl (W : Y.Opens) (x : (W : Scheme.{u}).presheaf.obj (op ⊤)) : uapp W (Iso.refl _) x = x := by
  simp only [uapp, Iso.refl_hom, SheafOfModules.id_val, PresheafOfModules.id_app]
  rfl

theorem unitAutSection_trans (W : Y.Opens)
    (e e' : SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf ≅ SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf) :
    unitAutSection W (e ≪≫ e') = unitAutSection W e * unitAutSection W e' := by
  rw [unitAutSection_eq, unitAutSection_eq, unitAutSection_eq, ← map_mul, uapp_trans, ← uapp_mul, mul_one]

theorem unitAutSection_refl (W : Y.Opens) :
    unitAutSection W (Iso.refl _) = 1 := by
  rw [unitAutSection_eq, uapp_refl, map_one]

theorem unitAutSection_symm_mul (W : Y.Opens)
    (e : SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf ≅ SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf) :
    unitAutSection W e.symm * unitAutSection W e = 1 := by
  rw [← unitAutSection_trans, Iso.symm_self_id, unitAutSection_refl]

theorem unitAutSection_mul_symm (W : Y.Opens)
    (e : SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf ≅ SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf) :
    unitAutSection W e * unitAutSection W e.symm = 1 := by
  rw [← unitAutSection_trans, Iso.self_symm_id, unitAutSection_refl]

theorem isUnit_unitAutSection (W : Y.Opens)
    (e : SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf ≅ SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf) :
    IsUnit (unitAutSection W e) :=
  ⟨⟨_, _, unitAutSection_mul_symm W e, unitAutSection_symm_mul W e⟩, rfl⟩

end AlgebraicGeometry.Scheme.Modules

namespace PV1TL

section coh

p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_comap_transition.AlgebraicGeometry.Scheme.Modules"

variable {T' T A' : Scheme.{u}}

lemma pullbackCongr_hom_app_eq {q q' : T ⟶ A'} (H : q = q') (N : A'.Modules) :
    (pullbackCongr H).hom.app N = eqToHom (by rw [H]) := by
  subst H; simp [pullbackCongr]

lemma pullbackCongr_inv_app_eq {q q' : T ⟶ A'} (H : q = q') (N : A'.Modules) :
    (pullbackCongr H).inv.app N = eqToHom (by rw [H]) := by
  subst H; simp [pullbackCongr]

lemma assoc_app {W : Scheme.{u}} (f : T' ⟶ T) (g : T ⟶ W) (h : W ⟶ A') (N : A'.Modules) :
    (Scheme.Modules.pullback f).map ((pullbackComp g h).inv.app N) ≫
      (pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj N) ≫ (pullbackComp (f ≫ g) h).hom.app N =
    (pullbackComp f (g ≫ h)).hom.app N ≫ eqToHom (by rw [Category.assoc]) := by
  have := NatTrans.congr_app (pseudofunctor_associativity f g h) N
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Category.id_comp, eqToHom_app] at this
  exact (Iso.inv_comp_eq ((pullbackComp f (g ≫ h)).app N)).1 this

lemma assoc_app'' {W : Scheme.{u}} (f : T' ⟶ T) (g : T ⟶ W) (h : W ⟶ A') (N : A'.Modules) :
    (Scheme.Modules.pullback f).map ((pullbackComp g h).inv.app N) =
      (pullbackComp f (g ≫ h)).hom.app N ≫ eqToHom (by rw [Category.assoc]) ≫ (pullbackComp (f ≫ g) h).inv.app N ≫
        (pullbackComp f g).inv.app ((Scheme.Modules.pullback h).obj N) := by
  have h1 := assoc_app f g h N
  let α : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback h).obj N)) ≅
      (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback (g ≫ h)).obj N) :=
    (Scheme.Modules.pullback f).mapIso ((pullbackComp g h).app N)
  let β : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback h).obj N)) ≅
      (Scheme.Modules.pullback (f ≫ g)).obj ((Scheme.Modules.pullback h).obj N) :=
    (pullbackComp f g).app ((Scheme.Modules.pullback h).obj N)
  let γ : (Scheme.Modules.pullback (f ≫ g)).obj ((Scheme.Modules.pullback h).obj N) ≅
      (Scheme.Modules.pullback ((f ≫ g) ≫ h)).obj N := (pullbackComp (f ≫ g) h).app N
  let δ : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback (g ≫ h)).obj N) ≅
      (Scheme.Modules.pullback (f ≫ g ≫ h)).obj N := (pullbackComp f (g ≫ h)).app N
  let η : (Scheme.Modules.pullback (f ≫ g ≫ h)).obj N ≅ (Scheme.Modules.pullback ((f ≫ g) ≫ h)).obj N :=
    eqToIso (by rw [Category.assoc])
  have h2 : α.symm ≪≫ β ≪≫ γ = δ ≪≫ η := Iso.ext h1
  have h3 : α.symm = δ ≪≫ η ≪≫ γ.symm ≪≫ β.symm := by
    calc α.symm = (α.symm ≪≫ β ≪≫ γ) ≪≫ (γ.symm ≪≫ β.symm) := by simp
      _ = (δ ≪≫ η) ≪≫ (γ.symm ≪≫ β.symm) := by rw [h2]
      _ = δ ≪≫ η ≪≫ γ.symm ≪≫ β.symm := by simp
  have h4 := congrArg Iso.hom h3
  simpa [α, β, γ, δ, η, eqToIso] using h4

lemma assoc_app' {W : Scheme.{u}} (f : T' ⟶ T) (g : T ⟶ W) (h : W ⟶ A') (N : A'.Modules) :
    (pullbackComp f g).inv.app ((Scheme.Modules.pullback h).obj N) ≫
      (Scheme.Modules.pullback f).map ((pullbackComp g h).hom.app N) =
    (pullbackComp (f ≫ g) h).hom.app N ≫ eqToHom (by rw [Category.assoc]) ≫ (pullbackComp f (g ≫ h)).inv.app N := by
  have h1 := assoc_app f g h N
  let α : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback h).obj N)) ≅
      (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback (g ≫ h)).obj N) :=
    (Scheme.Modules.pullback f).mapIso ((pullbackComp g h).app N)
  let β : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback h).obj N)) ≅
      (Scheme.Modules.pullback (f ≫ g)).obj ((Scheme.Modules.pullback h).obj N) :=
    (pullbackComp f g).app ((Scheme.Modules.pullback h).obj N)
  let γ : (Scheme.Modules.pullback (f ≫ g)).obj ((Scheme.Modules.pullback h).obj N) ≅
      (Scheme.Modules.pullback ((f ≫ g) ≫ h)).obj N := (pullbackComp (f ≫ g) h).app N
  let δ : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback (g ≫ h)).obj N) ≅
      (Scheme.Modules.pullback (f ≫ g ≫ h)).obj N := (pullbackComp f (g ≫ h)).app N
  let η : (Scheme.Modules.pullback (f ≫ g ≫ h)).obj N ≅ (Scheme.Modules.pullback ((f ≫ g) ≫ h)).obj N :=
    eqToIso (by rw [Category.assoc])
  have h2 : α.symm ≪≫ β ≪≫ γ = δ ≪≫ η := Iso.ext h1
  have h3 : β.symm ≪≫ α = γ ≪≫ η.symm ≪≫ δ.symm := by
    have h2' : β ≪≫ γ = α ≪≫ δ ≪≫ η := by
      rw [← h2]; simp
    calc β.symm ≪≫ α = β.symm ≪≫ α ≪≫ (δ ≪≫ η) ≪≫ (δ ≪≫ η).symm := by simp
      _ = β.symm ≪≫ (α ≪≫ δ ≪≫ η) ≪≫ (η.symm ≪≫ δ.symm) := by simp
      _ = β.symm ≪≫ (β ≪≫ γ) ≪≫ (η.symm ≪≫ δ.symm) := by rw [h2']
      _ = γ ≪≫ η.symm ≪≫ δ.symm := by simp
  have h4 := congrArg Iso.hom h3
  simpa [α, β, γ, δ, η, eqToIso] using h4

lemma comp_congr_right (f : T' ⟶ T) {g g' : T ⟶ A'} (H : g = g') (N : A'.Modules) :
    (pullbackComp f g).inv.app N ≫ eqToHom (by rw [H]) ≫ (pullbackComp f g').hom.app N =
      eqToHom (by rw [H]) := by
  subst H; simpa using (pullbackComp f g).inv_hom_id_app N

lemma comp_congr_left {f f' : T' ⟶ T} (H : f = f') (g : T ⟶ A') (N : A'.Modules) :
    (pullbackComp f g).inv.app N ≫
        eqToHom (show (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N) =
          (Scheme.Modules.pullback f').obj ((Scheme.Modules.pullback g).obj N) by rw [H]) =
      eqToHom (by rw [H]) ≫ (pullbackComp f' g).inv.app N := by
  subst H; simp

lemma congr_unit {f f' : T' ⟶ T} (H : f = f') :
    (pullbackCongr H).hom.app (SheafOfModules.unit T.ringCatSheaf) ≫ (pullbackUnitIso f').hom =
      (pullbackUnitIso f).hom := by
  subst H; simp [pullbackCongr]

lemma congr_nat {f f' : T' ⟶ T} (H : f = f') {M N : T.Modules} (φ : M ⟶ N) :
    (pullbackCongr H).hom.app M ≫ (Scheme.Modules.pullback f').map φ =
      (Scheme.Modules.pullback f).map φ ≫ (pullbackCongr H).hom.app N := by
  subst H; simp [pullbackCongr]

end coh

end PV1TL

namespace PV1TL
p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_comap_transition.AlgebraicGeometry.Scheme.Modules"

section G
variable {Y V B : Scheme.{u}} (𝓜 : Y.Modules)

noncomputable def genRestrict (ι : V ⟶ Y) (j : B ⟶ Y) (k : B ⟶ V) (e : k ≫ ι = j)
    (τ : (Scheme.Modules.pullback ι).obj 𝓜 ≅ SheafOfModules.unit V.ringCatSheaf) :
    (Scheme.Modules.pullback j).obj 𝓜 ≅ SheafOfModules.unit B.ringCatSheaf :=
  ((pullbackCongr e).app 𝓜).symm ≪≫ ((pullbackComp k ι).app 𝓜).symm ≪≫
    (Scheme.Modules.pullback k).mapIso τ ≪≫ pullbackUnitIso k

theorem genRestrict_comp (ι : V ⟶ Y) (j : B ⟶ Y) (k : B ⟶ V) (e : k ≫ ι = j)
    (τ : (Scheme.Modules.pullback ι).obj 𝓜 ≅ SheafOfModules.unit V.ringCatSheaf)
    {B' : Scheme.{u}} (q : B' ⟶ B) (j' : B' ⟶ Y) (e' : q ≫ j = j') (k' : B' ⟶ V) (Hk : q ≫ k = k')
    (e'' : k' ≫ ι = j') :
    genRestrict 𝓜 ι j' k' e'' τ =
      ((pullbackComp q j).app 𝓜 ≪≫ (pullbackCongr e').app 𝓜).symm ≪≫
        (Scheme.Modules.pullback q).mapIso (genRestrict 𝓜 ι j k e τ) ≪≫ pullbackUnitIso q := by
  subst e e' Hk
  have natinv := (pullbackComp q k).inv.naturality τ.hom
  simp only [Functor.comp_map] at natinv
  have u := Scheme.Modules.pullbackComp_hom_app_comp_pullbackUnitIso_hom q k
  apply Iso.ext
  simp only [genRestrict, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.app_inv, Functor.mapIso_hom,
    Functor.map_comp, pullbackCongr_inv_app_eq, eqToHom_refl, Category.id_comp]
  simp only [Functor.comp_obj, Category.assoc]
  erw [assoc_app'' q k ι 𝓜]
  simp only [Functor.comp_obj, Category.assoc, Iso.inv_hom_id_app_assoc]
  erw [← reassoc_of% natinv]
  erw [← u]
  erw [Iso.inv_hom_id_app_assoc]

end G

end PV1TL

namespace PV1TL
p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_comap_transition.AlgebraicGeometry.Scheme.Modules"

section isoAlgebra2
variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)

lemma pre_symm_trans_pre {M : C} {N U : D} {I : C} (P : N ≅ F.obj M) (ε : F.obj I ≅ U) (Ra Rb : M ≅ I) :
    (P ≪≫ F.mapIso Ra ≪≫ ε).symm ≪≫ (P ≪≫ F.mapIso Rb ≪≫ ε) =
      ε.symm ≪≫ F.mapIso (Ra.symm ≪≫ Rb) ≪≫ ε := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Category.assoc, Iso.inv_hom_id_assoc, Functor.map_comp]

end isoAlgebra2

section GG
variable {Y Y' V B B' : Scheme.{u}} (𝓜 : Y.Modules)

set_option maxHeartbeats 6400000 in

theorem genRestrict_pullback (h : Y' ⟶ Y) (ι : V ⟶ Y) (j₁ : B ⟶ Y') (k : B ⟶ V) (e : k ≫ ι = j₁ ≫ h)
    (τ : (Scheme.Modules.pullback ι).obj 𝓜 ≅ SheafOfModules.unit V.ringCatSheaf)
    (k₂ : B' ⟶ B) (j₂ : B' ⟶ Y') (e₂ : k₂ ≫ j₁ = j₂) (e₃ : (k₂ ≫ k) ≫ ι = j₂ ≫ h) :
    genRestrict ((Scheme.Modules.pullback h).obj 𝓜) j₁ j₂ k₂ e₂
        ((pullbackComp j₁ h).app 𝓜 ≪≫ genRestrict 𝓜 ι (j₁ ≫ h) k e τ) =
      (pullbackComp j₂ h).app 𝓜 ≪≫ genRestrict 𝓜 ι (j₂ ≫ h) (k₂ ≫ k) e₃ τ := by
  subst e₂
  have natinv := (pullbackComp k₂ k).inv.naturality τ.hom
  simp only [Functor.comp_map] at natinv
  have u := Scheme.Modules.pullbackComp_hom_app_comp_pullbackUnitIso_hom k₂ k
  apply Iso.ext
  simp only [genRestrict, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.app_inv, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, pullbackCongr_inv_app_eq, eqToHom_refl, Category.id_comp, eqToHom_map]
  simp only [Functor.comp_obj, Category.assoc]
  erw [assoc_app'' k₂ k ι 𝓜]
  simp only [Functor.comp_obj, Category.assoc]
  erw [← reassoc_of% natinv]
  erw [← u]
  erw [Iso.inv_hom_id_app_assoc]

  erw [reassoc_of% (assoc_app' k₂ j₁ h 𝓜)]
  erw [reassoc_of% (comp_congr_right k₂ e.symm 𝓜)]
  simp only [eqToHom_trans_assoc, Category.assoc]
  done

end GG

end PV1TL

namespace PV1TL
p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_comap_transition.AlgebraicGeometry.Scheme.Modules"

section conjGeneral
variable {X Z : Scheme.{u}} (φ : X ⟶ Z)

def toU (U : Z.Opens) (g : Z.presheaf.obj (op U)) :
    Γ((SheafOfModules.unit Z.ringCatSheaf : Z.Modules), U) := g

theorem pullbackUnitIso_hom_app_pls (U : Z.Opens) (g : Z.presheaf.obj (op U)) :
    (pullbackUnitIso φ).hom.app (φ ⁻¹ᵁ U) (pullbackLocalSection φ (toU U g)) =
      toU (φ ⁻¹ᵁ U) ((φ.app U).hom g) := by
  have h1 : (pullbackUnitIso φ).hom =
      ((pullbackPushforwardAdjunction φ).homEquiv _ _).symm
        (SheafOfModules.unitToPushforwardObjUnit φ.toRingCatSheafHom) := rfl
  rw [h1, Scheme.Modules.homEquiv_symm_app_pullbackLocalSection]
  rfl

theorem pullbackUnitIso_inv_app_one (U : Z.Opens) :
    (pullbackUnitIso φ).inv.app (φ ⁻¹ᵁ U) (toU (φ ⁻¹ᵁ U) 1) = pullbackLocalSection φ (toU U 1) := by
  have h := pullbackUnitIso_hom_app_pls φ U 1
  rw [map_one] at h
  rw [← h, ← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id, Scheme.Modules.Hom.id_app,
    CategoryTheory.id_apply]

end conjGeneral

variable {Y : Scheme.{u}}

noncomputable def uASm (W : Y.Opens)
    (E : @Iso ((W : Scheme.{u}).Modules) _ (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)
      (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)) : Γ(Y, W) :=
  unitAutSection W E

theorem uASm_eq (W : Y.Opens)
    (E : @Iso ((W : Scheme.{u}).Modules) _ (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)
      (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)) :
    uASm W E = W.topIso.hom.hom (uapp W E 1) := rfl

theorem uASm_conj_general {Y' : Scheme.{u}} {W : Y.Opens} {W'' : Y'.Opens}
    (q : (W'' : Scheme.{u}) ⟶ (W : Scheme.{u}))
    (E : @Iso ((W : Scheme.{u}).Modules) _ (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)
      (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)) :
    uASm W'' ((pullbackUnitIso q).symm ≪≫ (Scheme.Modules.pullback q).mapIso E ≪≫ pullbackUnitIso q) =
      W''.topIso.hom.hom (q.appTop.hom (uapp W E 1)) := by
  have step : uapp W'' (show @Iso ((W'' : Scheme.{u}).Modules) _ _ _ from
      (pullbackUnitIso q).symm ≪≫ (Scheme.Modules.pullback q).mapIso E ≪≫ pullbackUnitIso q) 1 =
      (q.appTop).hom (uapp W E 1) := by
    change ((pullbackUnitIso q).inv ≫ (Scheme.Modules.pullback q).map E.hom ≫
        (pullbackUnitIso q).hom).app (q ⁻¹ᵁ ⊤) (toU (q ⁻¹ᵁ ⊤) 1) =
      toU (q ⁻¹ᵁ ⊤) ((q.app ⊤).hom (Scheme.Modules.Hom.app E.hom ⊤ (toU ⊤ 1)))
    rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply,
      CategoryTheory.comp_apply, pullbackUnitIso_inv_app_one, ← pullbackLocalSection_app]
    exact pullbackUnitIso_hom_app_pls q ⊤ _
  rw [uASm_eq, step]

theorem uASm_conj_resLE {Y' : Scheme.{u}} (h : Y' ⟶ Y) {W : Y.Opens} {W'' : Y'.Opens} (c : W'' ≤ h ⁻¹ᵁ W)
    (E : @Iso ((W : Scheme.{u}).Modules) _ (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)
      (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)) :
    uASm W'' ((pullbackUnitIso (h.resLE W W'' c)).symm ≪≫
        (Scheme.Modules.pullback (h.resLE W W'' c)).mapIso E ≪≫ pullbackUnitIso (h.resLE W W'' c)) =
      (Y'.presheaf.map (homOfLE c).op).hom ((h.app W).hom (uASm W E)) := by
  rw [uASm_conj_general, uASm_eq, Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
  simp only [CategoryTheory.comp_apply, CategoryTheory.Iso.inv_hom_id_apply]
  rfl

variable {𝒱 : Y.OrderedAffineCover} {𝓜 : Y.Modules} (τ : CechTrivialisation 𝒱 𝓜)

theorem restrict_eq_genRestrict {a : 𝒱.ι} {W : Y.Opens} (hx : W ≤ 𝒱.U a) :
    τ.restrict hx = genRestrict 𝓜 (𝒱.U a).ι W.ι (Y.homOfLE hx) (Y.homOfLE_ι hx) (τ a) := rfl

variable {Y' : Scheme.{u}} (h : Y' ⟶ Y) [IsAffineHom h]

theorem comap_apply_eq (a : 𝒱.ι) :
    τ.comap h a = (pullbackComp (h ⁻¹ᵁ 𝒱.U a).ι h).app 𝓜 ≪≫
      genRestrict 𝓜 (𝒱.U a).ι ((h ⁻¹ᵁ 𝒱.U a).ι ≫ h) (h ∣_ 𝒱.U a) (morphismRestrict_ι h (𝒱.U a)) (τ a) := by
  first
    | rfl
    | (apply Iso.ext
       simp only [CechTrivialisation.comap, genRestrict, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
         Functor.mapIso_hom, pullbackCongr_hom_app_eq, pullbackCongr_inv_app_eq])

theorem comap_restrict_eq_genRestrict (a : 𝒱.ι) {W'' : Y'.Opens} (hx' : W'' ≤ (𝒱.comap h).U a) :
    (τ.comap h).restrict hx' =
      genRestrict ((Scheme.Modules.pullback h).obj 𝓜) (h ⁻¹ᵁ 𝒱.U a).ι W''.ι (Y'.homOfLE hx') (Y'.homOfLE_ι hx')
        (τ.comap h a) := rfl

noncomputable def Piso (𝓜 : Y.Modules) {W : Y.Opens} {W'' : Y'.Opens} (c : W'' ≤ h ⁻¹ᵁ W) :
    (Scheme.Modules.pullback W''.ι).obj ((Scheme.Modules.pullback h).obj 𝓜) ≅
      (Scheme.Modules.pullback (h.resLE W W'' c)).obj ((Scheme.Modules.pullback W.ι).obj 𝓜) :=
  (pullbackComp W''.ι h).app 𝓜 ≪≫
    ((pullbackComp (h.resLE W W'' c) W.ι).app 𝓜 ≪≫ (pullbackCongr (Scheme.Hom.resLE_comp_ι h c)).app 𝓜).symm

set_option maxHeartbeats 6400000 in
theorem comap_restrict (a : 𝒱.ι) {W : Y.Opens} (hx : W ≤ 𝒱.U a) {W'' : Y'.Opens} (c : W'' ≤ h ⁻¹ᵁ W)
    (hx' : W'' ≤ (𝒱.comap h).U a) :
    (τ.comap h).restrict hx' =
      Piso h 𝓜 c ≪≫ (Scheme.Modules.pullback (h.resLE W W'' c)).mapIso (τ.restrict hx) ≪≫
        pullbackUnitIso (h.resLE W W'' c) := by
  have e₃ : (Y'.homOfLE hx' ≫ h ∣_ 𝒱.U a) ≫ (𝒱.U a).ι = W''.ι ≫ h := Scheme.Hom.resLE_comp_ι h hx'
  have Hk : h.resLE W W'' c ≫ Y.homOfLE hx = Y'.homOfLE hx' ≫ h ∣_ 𝒱.U a := by
    rw [Scheme.Hom.resLE_map]; rfl
  have step1 : (τ.comap h).restrict hx' =
      genRestrict ((Scheme.Modules.pullback h).obj 𝓜) (h ⁻¹ᵁ 𝒱.U a).ι W''.ι (Y'.homOfLE hx') (Y'.homOfLE_ι hx')
        ((pullbackComp (h ⁻¹ᵁ 𝒱.U a).ι h).app 𝓜 ≪≫
          genRestrict 𝓜 (𝒱.U a).ι ((h ⁻¹ᵁ 𝒱.U a).ι ≫ h) (h ∣_ 𝒱.U a) (morphismRestrict_ι h (𝒱.U a)) (τ a)) := by
    rw [comap_restrict_eq_genRestrict, comap_apply_eq]
  have step2 := genRestrict_pullback 𝓜 h (𝒱.U a).ι (h ⁻¹ᵁ 𝒱.U a).ι (h ∣_ 𝒱.U a) (morphismRestrict_ι h (𝒱.U a)) (τ a)
      (Y'.homOfLE hx') W''.ι (Y'.homOfLE_ι hx') e₃
  have step3 := genRestrict_comp 𝓜 (𝒱.U a).ι W.ι (Y.homOfLE hx) (Y.homOfLE_ι hx) (τ a) (h.resLE W W'' c) (W''.ι ≫ h)
      (Scheme.Hom.resLE_comp_ι h c) (Y'.homOfLE hx' ≫ h ∣_ 𝒱.U a) Hk e₃
  rw [step1]
  refine step2.trans ?_
  refine (congrArg (fun e => (pullbackComp W''.ι h).app 𝓜 ≪≫ e) step3).trans ?_
  rw [restrict_eq_genRestrict]
  simp only [Piso, Iso.trans_assoc]

theorem comap_transition (s : 𝒱.Idx 1) :
    (τ.comap h).transition s =
      (Y'.presheaf.map (homOfLE (𝒱.comap_inter_le h s)).op).hom ((h.app (𝒱.inter s)).hom (τ.transition s)) := by
  have e0 := comap_restrict τ h (s.1 0) (𝒱.inter_le s 0) (𝒱.comap_inter_le h s) ((𝒱.comap h).inter_le s 0)
  have e1 := comap_restrict τ h (s.1 1) (𝒱.inter_le s 1) (𝒱.comap_inter_le h s) ((𝒱.comap h).inter_le s 1)
  show uASm ((𝒱.comap h).inter s) (((τ.comap h).restrict ((𝒱.comap h).inter_le s 0)).symm ≪≫
      (τ.comap h).restrict ((𝒱.comap h).inter_le s 1)) =
    (Y'.presheaf.map (homOfLE (𝒱.comap_inter_le h s)).op).hom ((h.app (𝒱.inter s)).hom
      (uASm (𝒱.inter s) ((τ.restrict (𝒱.inter_le s 0)).symm ≪≫ τ.restrict (𝒱.inter_le s 1))))
  rw [e0, e1, pre_symm_trans_pre, uASm_conj_resLE]

end PV1TL

theorem solution
    {Y Y' : Scheme.{u}} (h : Y' ⟶ Y) [IsAffineHom h] (𝒱 : Y.OrderedAffineCover) (𝓜 : Y.Modules)
    (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓜) (s : 𝒱.Idx 1) :
    (τ.comap h).transition s =
      (Y'.presheaf.map (homOfLE (𝒱.comap_inter_le h s)).op).hom ((h.app (𝒱.inter s)).hom (τ.transition s)) :=
  PV1TL.comap_transition τ h s

end S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_comap_transition
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_comap_transition (solution)
