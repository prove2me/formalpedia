-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.unitAutSection_comap_refinement_eq_appLE
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/e5ebeb66-3e95-5fe0-992e-b51c731a0222

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_hom_app_comp_pullbackUnitIso_hom
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackUnitIso_conj_app_top_one_eq_appTop
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_unitAutSection_comap_refinement_eq_appLE

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_unitAutSection_comap_refinement_eq_appLE.AlgebraicGeometry Opposite TopologicalSpace"

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.resLE_comp_ι Scheme.Opens.topIso_inv morphismRestrict_ι Scheme.Modules.pullback Scheme.Hom Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Scheme Scheme.Modules.Hom.id_app Scheme.Modules.Hom.app Scheme.Hom.appTop Scheme.Opens.topIso_hom Scheme.homOfLE_homOfLE Scheme.Modules.pullbackCongr Scheme.homOfLE_app Scheme.Modules Scheme.Opens Scheme.homOfLE_ι Scheme.Hom.resLE_app_top Scheme.Hom.comp_preimage IsAffineHom Scheme.Hom.appLE Scheme.Modules.pullbackComp Scheme.Modules.pullbackUnitIso Scheme.Modules.unitAutSection Scheme.Modules.CechTrivialisation Scheme.Modules.homEquiv_symm_app_pullbackLocalSection Scheme.Modules.pullbackComp_hom_app_comp_pullbackUnitIso_hom Scheme.Modules.pullbackUnitIso_conj_app_top_one_eq_appTop"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.resLE_comp_ι Opens.topIso_inv ringCatSheaf Modules.pullback Hom.id_app Hom Γ Modules.Hom.comp_app Hom.app topIso_hom Modules.Hom topIso Modules.Hom.id_app Modules.Hom.app Hom.appTop Opens.topIso_hom homOfLE_homOfLE Hom.comp_app Modules.pullbackCongr homOfLE_app Modules Opens homOfLE_ι Hom.resLE_app_top Hom.comp_preimage restrict Hom.appLE PresheafOfModules Modules.pullbackComp OrderedAffineCover Modules.pullbackUnitIso Modules.unitAutSection Modules.CechTrivialisation Modules.homEquiv_symm_app_pullbackLocalSection Modules.pullbackComp_hom_app_comp_pullbackUnitIso_hom Modules.pullbackUnitIso_conj_app_top_one_eq_appTop"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "pseudofunctor pullback presheaf Hom.comp_app Hom pseudofunctor_associativity Hom.id_app Hom.app pullbackCongr pullbackPushforwardAdjunction restrict map_smul pullbackComp pullbackUnitIso unitAutSection CechTrivialisation CechTrivialisation.comap pullbackLocalSection pullbackLocalSection_app homEquiv_symm_app_pullbackLocalSection pullbackComp_hom_app_comp_pullbackUnitIso_hom pullbackUnitIso_conj_app_top_one_eq_appTop"
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

p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_unitAutSection_comap_refinement_eq_appLE.AlgebraicGeometry.Scheme.Modules"

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
    eqToHom_app] at this
  erw [Category.id_comp] at this
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
p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_unitAutSection_comap_refinement_eq_appLE.AlgebraicGeometry.Scheme.Modules"

section conj
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

end conj

variable {Y : Scheme.{u}}

noncomputable def uASm (W : Y.Opens)
    (E : @Iso ((W : Scheme.{u}).Modules) _ (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)
      (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)) : Γ(Y, W) :=
  unitAutSection W E

section uasMod
variable (W : Y.Opens)
  (E E' : @Iso ((W : Scheme.{u}).Modules) _ (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)
    (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf))

theorem uASm_trans : uASm W (E ≪≫ E') = uASm W E * uASm W E' := unitAutSection_trans W E E'

theorem isUnit_uASm : IsUnit (uASm W E) := isUnit_unitAutSection W E

theorem uASm_eq : uASm W E = W.topIso.hom.hom (uapp W E 1) := rfl

end uasMod

lemma presheaf_map_op_apply_eq {U V : Y.Opens} (f g : U ⟶ V) (x : Y.presheaf.obj (op V)) :
    (Y.presheaf.map f.op).hom x = (Y.presheaf.map g.op).hom x := by
  rw [Subsingleton.elim f g]

lemma presheaf_comp_apply_eq {U V V' W : Y.Opens} (f : V ⟶ U) (g : W ⟶ V) (f' : V' ⟶ U) (g' : W ⟶ V')
    (x : Y.presheaf.obj (op U)) :
    (Y.presheaf.map f.op ≫ Y.presheaf.map g.op).hom x = (Y.presheaf.map f'.op ≫ Y.presheaf.map g'.op).hom x := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, Subsingleton.elim (g ≫ f) (g' ≫ f')]

theorem unitAutSection_conj {W W' : Y.Opens} (h' : W' ≤ W)
    (E : @Iso ((W : Scheme.{u}).Modules) _ (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)
      (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)) :
    uASm W' ((pullbackUnitIso (Y.homOfLE h')).symm ≪≫
        (Scheme.Modules.pullback (Y.homOfLE h')).mapIso E ≪≫ pullbackUnitIso (Y.homOfLE h')) =
      (Y.presheaf.map (homOfLE h').op).hom (uASm W E) := by

  have step : uapp W' (show @Iso ((W' : Scheme.{u}).Modules) _ _ _ from
      (pullbackUnitIso (Y.homOfLE h')).symm ≪≫
      (Scheme.Modules.pullback (Y.homOfLE h')).mapIso E ≪≫ pullbackUnitIso (Y.homOfLE h')) 1 =
      ((Y.homOfLE h').appTop).hom (uapp W E 1) := by
    change ((pullbackUnitIso (Y.homOfLE h')).inv ≫ (Scheme.Modules.pullback (Y.homOfLE h')).map E.hom ≫
        (pullbackUnitIso (Y.homOfLE h')).hom).app ((Y.homOfLE h') ⁻¹ᵁ ⊤) (toU ((Y.homOfLE h') ⁻¹ᵁ ⊤) 1) =
      toU ((Y.homOfLE h') ⁻¹ᵁ ⊤) (((Y.homOfLE h').app ⊤).hom (Scheme.Modules.Hom.app E.hom ⊤ (toU ⊤ 1)))
    rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply,
      CategoryTheory.comp_apply, pullbackUnitIso_inv_app_one, ← pullbackLocalSection_app]
    exact pullbackUnitIso_hom_app_pls (Y.homOfLE h') ⊤ _
  rw [uASm_eq, uASm_eq, step]

  simp only [Scheme.Hom.appTop, Scheme.homOfLE_app, Scheme.Opens.topIso_hom, ← CategoryTheory.comp_apply]
  exact presheaf_comp_apply_eq _ _ _ _ _

end PV1TL

namespace PV1TL
p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_unitAutSection_comap_refinement_eq_appLE.AlgebraicGeometry.Scheme.Modules"

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
  simp only [Functor.comp_obj, Category.assoc]
  erw [← reassoc_of% natinv]
  erw [← u]
  erw [Iso.inv_hom_id_app_assoc]
  erw [Iso.inv_hom_id_app_assoc]

end G

end PV1TL

namespace PV1TL
p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_unitAutSection_comap_refinement_eq_appLE.AlgebraicGeometry.Scheme.Modules"

section isoAlgebra
variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)

lemma conj_symm_trans_conj {M : C} {N U : D} {I : C} (κ : F.obj M ≅ N) (ε : F.obj I ≅ U) (Ra Rb : M ≅ I) :
    (κ.symm ≪≫ F.mapIso Ra ≪≫ ε).symm ≪≫ (κ.symm ≪≫ F.mapIso Rb ≪≫ ε) =
      ε.symm ≪≫ F.mapIso (Ra.symm ≪≫ Rb) ≪≫ ε := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Category.assoc, Iso.hom_inv_id_assoc, Functor.map_comp]

lemma symm_trans_trans_symm_trans {M I : C} (Ra Rb Rc : M ≅ I) :
    (Ra.symm ≪≫ Rb) ≪≫ (Rb.symm ≪≫ Rc) = Ra.symm ≪≫ Rc := by
  simp

end isoAlgebra

variable {Y : Scheme.{u}}

variable {𝒱 : Y.OrderedAffineCover} {𝓜 : Y.Modules} (τ : CechTrivialisation 𝒱 𝓜)

theorem restrict_eq_genRestrict {a : 𝒱.ι} {W : Y.Opens} (h : W ≤ 𝒱.U a) :
    τ.restrict h = genRestrict 𝓜 (𝒱.U a).ι W.ι (Y.homOfLE h) (Y.homOfLE_ι h) (τ a) := rfl

noncomputable def κiso (𝓜 : Y.Modules) {W W' : Y.Opens} (h' : W' ≤ W) :
    (Scheme.Modules.pullback (Y.homOfLE h')).obj ((Scheme.Modules.pullback W.ι).obj 𝓜) ≅
      (Scheme.Modules.pullback W'.ι).obj 𝓜 :=
  (pullbackComp (Y.homOfLE h') W.ι).app 𝓜 ≪≫ (pullbackCongr (Y.homOfLE_ι h')).app 𝓜

theorem restrict_trans {a : 𝒱.ι} {W W' : Y.Opens} (h : W ≤ 𝒱.U a) (h' : W' ≤ W) :
    τ.restrict (h'.trans h) =
      (κiso 𝓜 h').symm ≪≫
        (Scheme.Modules.pullback (Y.homOfLE h')).mapIso (τ.restrict h) ≪≫ pullbackUnitIso (Y.homOfLE h') := by
  rw [restrict_eq_genRestrict, restrict_eq_genRestrict]
  exact genRestrict_comp 𝓜 (𝒱.U a).ι W.ι (Y.homOfLE h) (Y.homOfLE_ι h) (τ a) (Y.homOfLE h') W'.ι
    (Y.homOfLE_ι h') (Y.homOfLE (h'.trans h)) (Scheme.homOfLE_homOfLE Y h' h) (Y.homOfLE_ι (h'.trans h))

noncomputable def θ (W : Y.Opens) (a b : 𝒱.ι) (ha : W ≤ 𝒱.U a) (hb : W ≤ 𝒱.U b) : Γ(Y, W) :=
  uASm W ((τ.restrict ha).symm ≪≫ τ.restrict hb)

theorem transition_eq_θ (s : 𝒱.Idx 1) :
    τ.transition s = θ τ (𝒱.inter s) (s.1 0) (s.1 1) (𝒱.inter_le s 0) (𝒱.inter_le s 1) := rfl

theorem θ_res {W W' : Y.Opens} (h' : W' ≤ W) (a b : 𝒱.ι) (ha : W ≤ 𝒱.U a) (hb : W ≤ 𝒱.U b) :
    (Y.presheaf.map (homOfLE h').op).hom (θ τ W a b ha hb) = θ τ W' a b (h'.trans ha) (h'.trans hb) := by
  rw [θ, θ, restrict_trans τ ha h', restrict_trans τ hb h', conj_symm_trans_conj, unitAutSection_conj]

theorem θ_mul (W : Y.Opens) (a b c : 𝒱.ι) (ha : W ≤ 𝒱.U a) (hb hb' : W ≤ 𝒱.U b) (hc : W ≤ 𝒱.U c) :
    θ τ W a b ha hb * θ τ W b c hb' hc = θ τ W a c ha hc := by
  rw [θ, θ, θ, show τ.restrict hb' = τ.restrict hb from rfl, ← uASm_trans, symm_trans_trans_symm_trans]

theorem isUnit_transition (s : 𝒱.Idx 1) : IsUnit (τ.transition s) := by
  rw [transition_eq_θ]; exact isUnit_uASm _ _

theorem cocycle (r : 𝒱.Idx 2) :
    (Y.presheaf.map (homOfLE (𝒱.inter_le_inter_face r 2)).op).hom (τ.transition (𝒱.face r 2)) *
        (Y.presheaf.map (homOfLE (𝒱.inter_le_inter_face r 0)).op).hom (τ.transition (𝒱.face r 0)) =
      (Y.presheaf.map (homOfLE (𝒱.inter_le_inter_face r 1)).op).hom (τ.transition (𝒱.face r 1)) := by
  rw [transition_eq_θ, transition_eq_θ, transition_eq_θ, θ_res, θ_res, θ_res]
  exact θ_mul τ (𝒱.inter r) (r.1 0) (r.1 1) (r.1 2) _ _ _ _

end PV1TL

namespace PV1TLC4
p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_unitAutSection_comap_refinement_eq_appLE.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_unitAutSection_comap_refinement_eq_appLE.PV1TL"

section generic
variable {Y Y' : Scheme.{u}} (𝓜 : Y.Modules) (h : Y' ⟶ Y)

theorem genRestrict_congr_k {V B : Scheme.{u}} (ι : V ⟶ Y) (j : B ⟶ Y) {k k' : B ⟶ V} (H : k = k')
    (e : k ≫ ι = j) (e' : k' ≫ ι = j)
    (τc : (Scheme.Modules.pullback ι).obj 𝓜 ≅ SheafOfModules.unit V.ringCatSheaf) :
    genRestrict 𝓜 ι j k e τc = genRestrict 𝓜 ι j k' e' τc := by
  subst H; rfl

set_option backward.isDefEq.respectTransparency false in

theorem genRestrict_precomp {V V' B : Scheme.{u}} (ι : V ⟶ Y) (ι' : V' ⟶ Y') (k₁ : V' ⟶ V)
    (e₁ : k₁ ≫ ι = ι' ≫ h)
    (τc : (Scheme.Modules.pullback ι).obj 𝓜 ≅ SheafOfModules.unit V.ringCatSheaf)
    (j : B ⟶ Y') (k₂ : B ⟶ V') (e₂ : k₂ ≫ ι' = j) (e₃ : (k₂ ≫ k₁) ≫ ι = j ≫ h) :
    genRestrict ((Scheme.Modules.pullback h).obj 𝓜) ι' j k₂ e₂
        ((pullbackComp ι' h).app 𝓜 ≪≫ genRestrict 𝓜 ι (ι' ≫ h) k₁ e₁ τc) =
      (pullbackComp j h).app 𝓜 ≪≫ genRestrict 𝓜 ι (j ≫ h) (k₂ ≫ k₁) e₃ τc := by
  subst e₂
  have key := genRestrict_comp 𝓜 ι (ι' ≫ h) k₁ e₁ τc k₂ ((k₂ ≫ ι') ≫ h) (by rw [Category.assoc]) (k₂ ≫ k₁)
    rfl e₃
  rw [key]
  have A := assoc_app k₂ ι' h 𝓜

  have h4 : (pullbackComp k₂ ι').inv.app ((Scheme.Modules.pullback h).obj 𝓜) ≫
      (Scheme.Modules.pullback k₂).map ((pullbackComp ι' h).hom.app 𝓜) =
      (pullbackComp (k₂ ≫ ι') h).hom.app 𝓜 ≫
        eqToHom (show (Scheme.Modules.pullback ((k₂ ≫ ι') ≫ h)).obj 𝓜 = (Scheme.Modules.pullback (k₂ ≫ ι' ≫ h)).obj 𝓜
          by rw [Category.assoc]) ≫
        (pullbackComp k₂ (ι' ≫ h)).inv.app 𝓜 := by
    erw [← cancel_epi ((pullbackComp k₂ ι').hom.app ((Scheme.Modules.pullback h).obj 𝓜)),
      Iso.hom_inv_id_app_assoc]
    erw [← cancel_epi ((Scheme.Modules.pullback k₂).map ((pullbackComp ι' h).inv.app 𝓜)), ← Functor.map_comp,
      Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
    erw [reassoc_of% A]
    simp [eqToHom_trans]
  apply Iso.ext
  simp only [genRestrict, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, Functor.map_comp, pullbackCongr_inv_app_eq,
    eqToHom_refl, Category.id_comp, Category.assoc]
  erw [reassoc_of% h4]
  simp only [Category.assoc, eqToHom_refl, Category.id_comp]

end generic

section comapAsGen
variable {Y Y' : Scheme.{u}} {𝒱 : Y.OrderedAffineCover} {𝓜 : Y.Modules} (τ : CechTrivialisation 𝒱 𝓜)
  (h : Y' ⟶ Y) [IsAffineHom h]

theorem comap_eq_genRestrict (c : 𝒱.ι) :
    τ.comap h c = (pullbackComp (h ⁻¹ᵁ 𝒱.U c).ι h).app 𝓜 ≪≫
      genRestrict 𝓜 (𝒱.U c).ι ((h ⁻¹ᵁ 𝒱.U c).ι ≫ h) (h ∣_ 𝒱.U c) (morphismRestrict_ι h (𝒱.U c)) (τ c) := by
  apply Iso.ext
  simp only [CechTrivialisation.comap, genRestrict, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, pullbackCongr_hom_app_eq, pullbackCongr_inv_app_eq]
  rfl

end comapAsGen

end PV1TLC4

namespace FFT2
p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_unitAutSection_comap_refinement_eq_appLE.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_unitAutSection_comap_refinement_eq_appLE.PV1TL P2MW.S_AlgebraicGeometry_Scheme_Modules_unitAutSection_comap_refinement_eq_appLE.PV1TLC4"

section generic
variable {Y V B : Scheme.{u}} (𝓜 : Y.Modules)

theorem pullbackComp_trans_genRestrict_rfl (ι : V ⟶ Y) (k : B ⟶ V)
    (τc : (Scheme.Modules.pullback ι).obj 𝓜 ≅ SheafOfModules.unit V.ringCatSheaf) :
    (pullbackComp k ι).app 𝓜 ≪≫ genRestrict 𝓜 ι (k ≫ ι) k rfl τc =
      (Scheme.Modules.pullback k).mapIso τc ≪≫ pullbackUnitIso k := by
  apply Iso.ext
  simp only [genRestrict, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    pullbackCongr_inv_app_eq, eqToHom_refl, Category.id_comp]
  exact (pullbackComp k ι).hom_inv_id_app_assoc _ _

lemma trans_symm_trans_trans {C : Type*} [Category C] {P Q R : C} (c : P ≅ Q) (G₁ G₂ : Q ≅ R) :
    (c ≪≫ G₁).symm ≪≫ (c ≪≫ G₂) = G₁.symm ≪≫ G₂ := by
  apply Iso.ext; simp

end generic

section lemmaB
variable {Y Y' : Scheme.{u}} (h : Y' ⟶ Y)

theorem appLE_uASm {W : Y.Opens} {W' : Y'.Opens} (hle : W' ≤ h ⁻¹ᵁ W)
    (E : @Iso ((W : Scheme.{u}).Modules) _ (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)
      (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)) :
    (h.appLE W W' hle).hom (uASm W E) =
      uASm W' ((pullbackUnitIso (h.resLE W W' hle)).symm ≪≫
        (Scheme.Modules.pullback (h.resLE W W' hle)).mapIso E ≪≫ pullbackUnitIso (h.resLE W W' hle)) := by
  have step := AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_conj_app_top_one_eq_appTop (h.resLE W W' hle) E
  rw [uASm_eq, uASm_eq]
  change _ = W'.topIso.hom.hom (((show SheafOfModules.unit (W' : Scheme.{u}).ringCatSheaf ≅
      SheafOfModules.unit (W' : Scheme.{u}).ringCatSheaf from
      (pullbackUnitIso (h.resLE W W' hle)).symm ≪≫
        (Scheme.Modules.pullback (h.resLE W W' hle)).mapIso E ≪≫ pullbackUnitIso (h.resLE W W' hle)).hom.val.app
          (op ⊤)).hom (1 : (W' : Scheme.{u}).presheaf.obj (op ⊤)))
  erw [step]
  simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Scheme.Opens.topIso_hom, Scheme.Opens.topIso_inv,
    Scheme.Hom.appLE, ← CategoryTheory.comp_apply]
  have key : ∀ {U U' : Y'.Opens} (a : U' ⟶ U) (b : U ⟶ U') (z : Y'.presheaf.obj (op U)),
      (Y'.presheaf.map b.op).hom ((Y'.presheaf.map a.op).hom z) = z := by
    intro U U' a b z
    rw [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp, Subsingleton.elim (b ≫ a) (𝟙 _), op_id,
      CategoryTheory.Functor.map_id]
    rfl
  simp only [Category.assoc, CategoryTheory.comp_apply]
  erw [key]
  rfl

end lemmaB

theorem core {X X' X₀ X₀' : Scheme.{u}}
    (g : X₀ ⟶ X) (g' : X₀' ⟶ X') (h : X' ⟶ X) (h₀ : X₀' ⟶ X₀) (hh₀ : h₀ ≫ g = g' ≫ h)
    (M : X.Modules) (U : X.Opens) (Ww : X'.Opens) (U' : X₀.Opens) (W' : X₀'.Opens)
    (gU : (U' : Scheme.{u}) ⟶ (U : Scheme.{u})) (egU : gU ≫ U.ι = U'.ι ≫ g)
    (gW : (W' : Scheme.{u}) ⟶ (Ww : Scheme.{u})) (egW : gW ≫ Ww.ι = W'.ι ≫ g')
    (r : (Ww : Scheme.{u}) ⟶ (U : Scheme.{u})) (e₁ : r ≫ U.ι = Ww.ι ≫ h)
    (hle : W' ≤ h₀ ⁻¹ᵁ U')
    (τa : (Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)
    (φ₀ : (Scheme.Modules.pullback g).obj M ≅ SheafOfModules.unit X₀.ringCatSheaf)
    (TW : (Scheme.Modules.pullback W'.ι).obj ((Scheme.Modules.pullback g').obj ((Scheme.Modules.pullback h).obj M)) ≅
      SheafOfModules.unit (W' : Scheme.{u}).ringCatSheaf)
    (hTW : TW = (pullbackComp W'.ι g').app ((Scheme.Modules.pullback h).obj M) ≪≫
      genRestrict ((Scheme.Modules.pullback h).obj M) Ww.ι (W'.ι ≫ g') gW egW
        ((pullbackComp Ww.ι h).app M ≪≫ genRestrict M U.ι (Ww.ι ≫ h) r e₁ τa))
    (TU : (Scheme.Modules.pullback U'.ι).obj ((Scheme.Modules.pullback g).obj M) ≅
      SheafOfModules.unit (U' : Scheme.{u}).ringCatSheaf)
    (hTU : TU = (pullbackComp U'.ι g).app M ≪≫ genRestrict M U.ι (U'.ι ≫ g) gU egU τa) :
    uASm W' (TW.symm ≪≫ ((Scheme.Modules.pullback W'.ι).mapIso
        ((pullbackComp g' h).app M ≪≫ (pullbackCongr hh₀.symm).app M ≪≫ ((pullbackComp h₀ g).app M).symm ≪≫
          (Scheme.Modules.pullback h₀).mapIso φ₀ ≪≫ pullbackUnitIso h₀) ≪≫ pullbackUnitIso W'.ι)) =
      (h₀.appLE U' W' hle).hom (uASm U' (TU.symm ≪≫
        ((Scheme.Modules.pullback U'.ι).mapIso φ₀ ≪≫ pullbackUnitIso U'.ι))) := by
  subst hTW hTU
  have Hp : h₀.resLE U' W' hle ≫ U'.ι = W'.ι ≫ h₀ := Scheme.Hom.resLE_comp_ι h₀ hle
  have e' : h₀.resLE U' W' hle ≫ (U'.ι ≫ g) = (W'.ι ≫ g') ≫ h := by
    rw [← Category.assoc, Hp, Category.assoc, hh₀, Category.assoc]
  have Hk1 : h₀.resLE U' W' hle ≫ gU = gW ≫ r := by
    rw [← cancel_mono U.ι]
    simp only [Category.assoc]
    rw [egU, e₁, reassoc_of% Hp, reassoc_of% egW, hh₀]
  have e₃ : (gW ≫ r) ≫ U.ι = (W'.ι ≫ g') ≫ h := by rw [Category.assoc, e₁, ← Category.assoc, egW]
  have e₃' : (W'.ι ≫ h₀) ≫ g = (W'.ι ≫ g') ≫ h := by rw [Category.assoc, hh₀, Category.assoc]
  have hΦ : ((pullbackComp g' h).app M ≪≫ (pullbackCongr hh₀.symm).app M ≪≫ ((pullbackComp h₀ g).app M).symm ≪≫
        (Scheme.Modules.pullback h₀).mapIso φ₀ ≪≫ pullbackUnitIso h₀) =
      (pullbackComp g' h).app M ≪≫ genRestrict M g (g' ≫ h) h₀ hh₀ φ₀ := by
    apply Iso.ext
    simp only [genRestrict, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
      pullbackCongr_hom_app_eq, pullbackCongr_inv_app_eq]

  rw [genRestrict_precomp M h U.ι Ww.ι r e₁ τa (W'.ι ≫ g') gW egW e₃]
  rw [← pullbackComp_trans_genRestrict_rfl M g U'.ι φ₀]
  erw [hΦ]
  erw [← pullbackComp_trans_genRestrict_rfl ((Scheme.Modules.pullback h).obj M) g' W'.ι]
  erw [genRestrict_precomp M h g g' h₀ hh₀ φ₀ (W'.ι ≫ g') W'.ι rfl e₃']
  dsimp only [Functor.comp_obj]
  simp only [trans_symm_trans_trans]

  rw [genRestrict_comp M U.ι (U'.ι ≫ g) gU egU τa (h₀.resLE U' W' hle) ((W'.ι ≫ g') ≫ h) e' (gW ≫ r) Hk1 e₃]
  rw [genRestrict_comp M g (U'.ι ≫ g) U'.ι rfl φ₀ (h₀.resLE U' W' hle) ((W'.ι ≫ g') ≫ h) e' (W'.ι ≫ h₀) Hp e₃']
  try dsimp only [Functor.comp_obj]
  simp only [conj_symm_trans_conj]
  exact (appLE_uASm h₀ hle _).symm

end FFT2

open _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_unitAutSection_comap_refinement_eq_appLE.AlgebraicGeometry.Scheme.Modules PV1TL PV1TLC4 FFT2 in
theorem solution
    {X X' X₀ X₀' : Scheme.{u}}
    (g : X₀ ⟶ X) [IsAffineHom g] (g' : X₀' ⟶ X') [IsAffineHom g']
    (h : X' ⟶ X) (h₀ : X₀' ⟶ X₀) (hh₀ : h₀ ≫ g = g' ≫ h)
    (𝒰 : X.OrderedAffineCover) (𝒲 : X'.OrderedAffineCover) (lam : 𝒲.ι → 𝒰.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒰.U (lam w))
    (M : X.Modules) (τ : Scheme.Modules.CechTrivialisation 𝒰 M)
    (τ' : Scheme.Modules.CechTrivialisation 𝒲 ((Scheme.Modules.pullback h).obj M))
    (w : 𝒲.ι) (hτ' : τ' w = (((Scheme.Modules.pullbackComp (𝒲.U w).ι h).app M) ≪≫
          ((Scheme.Modules.pullbackCongr
              (show (𝒲.U w).ι ≫ h = (X'.homOfLE (hlam w) ≫ (h ∣_ 𝒰.U (lam w))) ≫ (𝒰.U (lam w)).ι by
                rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι])).app M) ≪≫
          ((Scheme.Modules.pullbackComp (X'.homOfLE (hlam w) ≫ (h ∣_ 𝒰.U (lam w))) (𝒰.U (lam w)).ι).app M).symm ≪≫
          (Scheme.Modules.pullback (X'.homOfLE (hlam w) ≫ (h ∣_ 𝒰.U (lam w)))).mapIso (τ (lam w)) ≪≫
          Scheme.Modules.pullbackUnitIso (X'.homOfLE (hlam w) ≫ (h ∣_ 𝒰.U (lam w)))))
    (φ₀ : (Scheme.Modules.pullback g).obj M ≅ SheafOfModules.unit X₀.ringCatSheaf) :
    Scheme.Modules.unitAutSection ((𝒲.comap g').U w)
        ((τ'.comap g' w).symm ≪≫
          ((Scheme.Modules.pullback ((𝒲.comap g').U w).ι).mapIso (((Scheme.Modules.pullbackComp g' h).app M) ≪≫
          ((Scheme.Modules.pullbackCongr hh₀.symm).app M) ≪≫
          ((Scheme.Modules.pullbackComp h₀ g).app M).symm ≪≫
          (Scheme.Modules.pullback h₀).mapIso φ₀ ≪≫
          Scheme.Modules.pullbackUnitIso h₀) ≪≫
            Scheme.Modules.pullbackUnitIso ((𝒲.comap g').U w).ι)) =
      (h₀.appLE ((𝒰.comap g).U (lam w)) ((𝒲.comap g').U w)
          (show g' ⁻¹ᵁ 𝒲.U w ≤ h₀ ⁻¹ᵁ (g ⁻¹ᵁ 𝒰.U (lam w)) by
            rw [← Scheme.Hom.comp_preimage, hh₀, Scheme.Hom.comp_preimage]
            exact fun p hp => hlam w hp)).hom
        (Scheme.Modules.unitAutSection ((𝒰.comap g).U (lam w))
          ((τ.comap g (lam w)).symm ≪≫
            ((Scheme.Modules.pullback ((𝒰.comap g).U (lam w)).ι).mapIso φ₀ ≪≫
              Scheme.Modules.pullbackUnitIso ((𝒰.comap g).U (lam w)).ι))) := by
  have e₁ : (X'.homOfLE (hlam w) ≫ (h ∣_ 𝒰.U (lam w))) ≫ (𝒰.U (lam w)).ι = (𝒲.U w).ι ≫ h := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
  have hτ'w : τ' w = (pullbackComp (𝒲.U w).ι h).app M ≪≫
      genRestrict M (𝒰.U (lam w)).ι ((𝒲.U w).ι ≫ h) (X'.homOfLE (hlam w) ≫ (h ∣_ 𝒰.U (lam w))) e₁ (τ (lam w)) := by
    rw [hτ']
    apply Iso.ext
    simp only [genRestrict, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
      pullbackCongr_hom_app_eq, pullbackCongr_inv_app_eq]
  exact core g g' h h₀ hh₀ M (𝒰.U (lam w)) (𝒲.U w) ((𝒰.comap g).U (lam w)) ((𝒲.comap g').U w)
    (g ∣_ 𝒰.U (lam w)) (morphismRestrict_ι g (𝒰.U (lam w))) (g' ∣_ 𝒲.U w) (morphismRestrict_ι g' (𝒲.U w))
    (X'.homOfLE (hlam w) ≫ (h ∣_ 𝒰.U (lam w))) e₁ _ (τ (lam w)) φ₀
    (τ'.comap g' w) (by rw [comap_eq_genRestrict τ' g' w, hτ'w]; rfl) (τ.comap g (lam w)) (comap_eq_genRestrict τ g (lam w))

end S_AlgebraicGeometry_Scheme_Modules_unitAutSection_comap_refinement_eq_appLE
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_unitAutSection_comap_refinement_eq_appLE (solution)
