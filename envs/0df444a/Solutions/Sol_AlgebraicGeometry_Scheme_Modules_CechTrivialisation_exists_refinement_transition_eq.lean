-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.CechTrivialisation.exists_refinement_transition_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/3f529c73-cb8e-5009-8cc1-58ebfe6dd94a

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_hom_app_comp_pullbackUnitIso_hom
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackUnitIso_conj_app_top_one_eq_appTop
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_refinement_transition_eq

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_refinement_transition_eq.AlgebraicGeometry Opposite TopologicalSpace"

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.resLE_comp_ι Scheme.Opens.topIso_inv morphismRestrict_ι Scheme.Modules.pullback Scheme.Hom Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Scheme Scheme.Modules.Hom.id_app Scheme.Modules.Hom.app Scheme.Hom.appTop Scheme.Opens.topIso_hom Scheme.homOfLE_homOfLE Scheme.Modules.pullbackCongr Scheme.homOfLE_app Scheme.Modules Scheme.Opens Scheme.homOfLE_ι Scheme.Hom.resLE_app_top Scheme.Hom.appLE Scheme.Modules.pullbackComp Scheme.Modules.pullbackUnitIso Scheme.Modules.CechTrivialisation Scheme.Modules.homEquiv_symm_app_pullbackLocalSection Scheme.Modules.pullbackComp_hom_app_comp_pullbackUnitIso_hom Scheme.Modules.pullbackUnitIso_conj_app_top_one_eq_appTop"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.resLE_comp_ι Opens.topIso_inv ringCatSheaf Modules.pullback Hom.id_app Hom Γ Modules.Hom.comp_app Hom.app topIso_hom Modules.Hom topIso Modules.Hom.id_app Modules.Hom.app Hom.appTop Opens.topIso_hom homOfLE_homOfLE Hom.comp_app Modules.pullbackCongr homOfLE_app Modules Opens homOfLE_ι Hom.resLE_app_top restrict Hom.appLE PresheafOfModules Modules.pullbackComp OrderedAffineCover Modules.pullbackUnitIso Modules.CechTrivialisation Modules.homEquiv_symm_app_pullbackLocalSection Modules.pullbackComp_hom_app_comp_pullbackUnitIso_hom Modules.pullbackUnitIso_conj_app_top_one_eq_appTop"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "pullback presheaf Hom.comp_app Hom pseudofunctor_associativity Hom.id_app Hom.app pullbackCongr pullbackPushforwardAdjunction restrict map_smul pullbackComp pullbackUnitIso unitAutSection CechTrivialisation pullbackLocalSection pullbackLocalSection_app homEquiv_symm_app_pullbackLocalSection pullbackComp_hom_app_comp_pullbackUnitIso_hom pullbackUnitIso_conj_app_top_one_eq_appTop"
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

p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_refinement_transition_eq.AlgebraicGeometry.Scheme.Modules"

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
p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_refinement_transition_eq.AlgebraicGeometry.Scheme.Modules"

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
p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_refinement_transition_eq.AlgebraicGeometry.Scheme.Modules"

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
p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_refinement_transition_eq.AlgebraicGeometry.Scheme.Modules"

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
p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_refinement_transition_eq.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_refinement_transition_eq.PV1TL"

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

end PV1TLC4

namespace PV1TLT1
p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_refinement_transition_eq.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_refinement_transition_eq.PV1TL P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_refinement_transition_eq.PV1TLC4"

section isoAlgebra
variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)

lemma trans_symm_trans_trans {A B U U' : C} (c : A ≅ B) (G₀ : B ≅ U) (G₁ : B ≅ U') :
    (c ≪≫ G₀).symm ≪≫ (c ≪≫ G₁) = G₀.symm ≪≫ G₁ := by
  apply Iso.ext; simp

lemma conj_trans_conj_eq_refl {I : C} {U : D} (ε : F.obj I ≅ U) {M : C} (Ra Rb : M ≅ I) :
    (ε.symm ≪≫ F.mapIso (Rb.symm ≪≫ Ra) ≪≫ ε) ≪≫ (ε.symm ≪≫ F.mapIso (Ra.symm ≪≫ Rb) ≪≫ ε) = Iso.refl _ := by
  apply Iso.ext
  simp

end isoAlgebra

variable {X Y : Scheme.{u}}

theorem uASm_eq_one_of_eq_refl (W : X.Opens)
    (E : @Iso ((W : Scheme.{u}).Modules) _ (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)
      (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)) (hE : E = Iso.refl _) :
    uASm W E = 1 := by
  subst hE; exact unitAutSection_refl W

theorem uASm_symm_self (W : X.Opens) {A : (W : Scheme.{u}).Modules}
    (G : A ≅ SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf) : uASm W (G.symm ≪≫ G) = 1 :=
  uASm_eq_one_of_eq_refl W _ (Iso.symm_self_id G)

lemma topIso_hom_inv_apply (U : X.Opens) (x : Γ(X, U)) : U.topIso.hom.hom (U.topIso.inv.hom x) = x := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id, RingHom.id_apply]

theorem uASm_resLE (h : X ⟶ Y) {W : Y.Opens} {W' : X.Opens} (hle : W' ≤ h ⁻¹ᵁ W)
    (E : @Iso ((W : Scheme.{u}).Modules) _ (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)
      (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)) :
    (X.presheaf.map (homOfLE hle).op).hom ((h.app W).hom (uASm W E)) =
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
  have key : ∀ {U U' : X.Opens} (a : U' ⟶ U) (b : U ⟶ U') (z : X.presheaf.obj (op U)),
      (X.presheaf.map b.op).hom ((X.presheaf.map a.op).hom z) = z := by
    intro U U' a b z
    rw [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp, Subsingleton.elim (b ≫ a) (𝟙 _), op_id,
      CategoryTheory.Functor.map_id]
    rfl
  simp only [Category.assoc, CategoryTheory.comp_apply]
  erw [key]
  rfl

theorem sortIdx_fin_two (h : X ⟶ Y) (𝒱 : Y.OrderedAffineCover) (𝒲 : X.OrderedAffineCover) (lam : 𝒲.ι → 𝒱.ι)
    (s : 𝒲.Idx 1) (hinj : Function.Injective (lam ∘ s.1)) :
    (lam (s.1 0) < lam (s.1 1) →
      (𝒲.sortIdx 𝒱 lam s hinj).1 0 = lam (s.1 0) ∧ (𝒲.sortIdx 𝒱 lam s hinj).1 1 = lam (s.1 1)) ∧
    (lam (s.1 1) < lam (s.1 0) →
      (𝒲.sortIdx 𝒱 lam s hinj).1 0 = lam (s.1 1) ∧ (𝒲.sortIdx 𝒱 lam s hinj).1 1 = lam (s.1 0)) := by
  have e0 : (𝒲.sortIdx 𝒱 lam s hinj).1 0 = lam (s.1 (Tuple.sort (lam ∘ s.1) 0)) := rfl
  have e1 : (𝒲.sortIdx 𝒱 lam s hinj).1 1 = lam (s.1 (Tuple.sort (lam ∘ s.1) 1)) := rfl
  have hm : (𝒲.sortIdx 𝒱 lam s hinj).1 0 < (𝒲.sortIdx 𝒱 lam s hinj).1 1 :=
    (𝒲.sortIdx 𝒱 lam s hinj).2 (show (0 : Fin 2) < 1 by decide)
  have hσ : Tuple.sort (lam ∘ s.1) 0 ≠ Tuple.sort (lam ∘ s.1) 1 :=
    fun H => absurd ((Tuple.sort (lam ∘ s.1)).injective H) (by decide)
  have two : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
  rcases two (Tuple.sort (lam ∘ s.1) 0) with h0 | h0 <;> rcases two (Tuple.sort (lam ∘ s.1) 1) with h1 | h1
  · exact absurd (h0.trans h1.symm) hσ
  · rw [h0] at e0; rw [h1] at e1
    rw [e0, e1] at hm
    exact ⟨fun _ => ⟨e0, e1⟩, fun hlt => absurd (hlt.trans hm) (lt_irrefl _)⟩
  · rw [h0] at e0; rw [h1] at e1
    rw [e0, e1] at hm
    exact ⟨fun hlt => absurd (hlt.trans hm) (lt_irrefl _), fun _ => ⟨e0, e1⟩⟩
  · exact absurd (h0.trans h1.symm) hσ

section main
variable (h : X ⟶ Y) (𝒱 : Y.OrderedAffineCover) (𝒲 : X.OrderedAffineCover) (lam : 𝒲.ι → 𝒱.ι)
  (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒱.U (lam w)) (𝓜 : Y.Modules) (τ : CechTrivialisation 𝒱 𝓜)

noncomputable def jw (w : 𝒲.ι) : (𝒲.U w : Scheme.{u}) ⟶ (𝒱.U (lam w) : Scheme.{u}) :=
  X.homOfLE (hlam w) ≫ h ∣_ 𝒱.U (lam w)

theorem jw_ι (w : 𝒲.ι) : jw h 𝒱 𝒲 lam hlam w ≫ (𝒱.U (lam w)).ι = (𝒲.U w).ι ≫ h := by
  rw [jw, Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]

noncomputable def tauP : CechTrivialisation 𝒲 ((Scheme.Modules.pullback h).obj 𝓜) := fun w =>
  (pullbackComp (𝒲.U w).ι h).app 𝓜 ≪≫
    genRestrict 𝓜 (𝒱.U (lam w)).ι ((𝒲.U w).ι ≫ h) (jw h 𝒱 𝒲 lam hlam w) (jw_ι h 𝒱 𝒲 lam hlam w) (τ (lam w))

theorem genRestrict_chart_congr {B : Scheme.{u}} {a b : 𝒱.ι} (hab : a = b) (j : B ⟶ Y)
    (k : B ⟶ (𝒱.U a : Scheme.{u})) (k' : B ⟶ (𝒱.U b : Scheme.{u}))
    (e : k ≫ (𝒱.U a).ι = j) (e' : k' ≫ (𝒱.U b).ι = j) :
    genRestrict 𝓜 (𝒱.U a).ι j k e (τ a) = genRestrict 𝓜 (𝒱.U b).ι j k' e' (τ b) := by
  subst hab
  obtain rfl : k = k' := by rw [← cancel_mono (𝒱.U a).ι]; exact e.trans e'.symm
  rfl

theorem tauP_restrict (w : 𝒲.ι) {W' : X.Opens} (hle : W' ≤ 𝒲.U w) :
    (tauP h 𝒱 𝒲 lam hlam 𝓜 τ).restrict hle =
      (pullbackComp W'.ι h).app 𝓜 ≪≫
        genRestrict 𝓜 (𝒱.U (lam w)).ι (W'.ι ≫ h) (X.homOfLE hle ≫ jw h 𝒱 𝒲 lam hlam w)
          (by rw [Category.assoc, jw_ι, ← Category.assoc, Scheme.homOfLE_ι]) (τ (lam w)) := by
  rw [restrict_eq_genRestrict]
  exact genRestrict_precomp 𝓜 h (𝒱.U (lam w)).ι (𝒲.U w).ι (jw h 𝒱 𝒲 lam hlam w) (jw_ι h 𝒱 𝒲 lam hlam w)
    (τ (lam w)) W'.ι (X.homOfLE hle) (X.homOfLE_ι hle) _

theorem tauP_transition (s : 𝒲.Idx 1) :
    (tauP h 𝒱 𝒲 lam hlam 𝓜 τ).transition s =
      uASm (𝒲.inter s)
        ((genRestrict 𝓜 (𝒱.U (lam (s.1 0))).ι ((𝒲.inter s).ι ≫ h)
            (X.homOfLE (𝒲.inter_le s 0) ≫ jw h 𝒱 𝒲 lam hlam (s.1 0))
            (by rw [Category.assoc, jw_ι, ← Category.assoc, Scheme.homOfLE_ι]) (τ (lam (s.1 0)))).symm ≪≫
          genRestrict 𝓜 (𝒱.U (lam (s.1 1))).ι ((𝒲.inter s).ι ≫ h)
            (X.homOfLE (𝒲.inter_le s 1) ≫ jw h 𝒱 𝒲 lam hlam (s.1 1))
            (by rw [Category.assoc, jw_ι, ← Category.assoc, Scheme.homOfLE_ι]) (τ (lam (s.1 1)))) := by
  rw [transition_eq_θ, θ, tauP_restrict, tauP_restrict]
  refine congrArg (uASm (𝒲.inter s)) ?_
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.app_hom, Iso.app_inv]
  erw [Category.assoc, Iso.inv_hom_id_app_assoc]
  try rfl

theorem clause_T0 (s : 𝒲.Idx 1) (hs : lam (s.1 0) = lam (s.1 1)) :
    (tauP h 𝒱 𝒲 lam hlam 𝓜 τ).transition s = 1 := by
  rw [tauP_transition,
    genRestrict_chart_congr 𝒱 𝓜 τ hs ((𝒲.inter s).ι ≫ h) _ (X.homOfLE (𝒲.inter_le s 1) ≫ jw h 𝒱 𝒲 lam hlam (s.1 1)) _
      (by rw [Category.assoc, jw_ι, ← Category.assoc, Scheme.homOfLE_ι])]
  exact uASm_symm_self _ _

theorem symm_trans_eq_conj (s : 𝒲.Idx 1) (t : 𝒱.Idx 1) (hWt : 𝒲.inter s ≤ h ⁻¹ᵁ 𝒱.inter t)
    (i₀ i₁ : Fin 2) (h₀ : t.1 i₀ = lam (s.1 0)) (h₁ : t.1 i₁ = lam (s.1 1)) :
    (genRestrict 𝓜 (𝒱.U (lam (s.1 0))).ι ((𝒲.inter s).ι ≫ h)
            (X.homOfLE (𝒲.inter_le s 0) ≫ jw h 𝒱 𝒲 lam hlam (s.1 0))
            (by rw [Category.assoc, jw_ι, ← Category.assoc, Scheme.homOfLE_ι]) (τ (lam (s.1 0)))).symm ≪≫
          genRestrict 𝓜 (𝒱.U (lam (s.1 1))).ι ((𝒲.inter s).ι ≫ h)
            (X.homOfLE (𝒲.inter_le s 1) ≫ jw h 𝒱 𝒲 lam hlam (s.1 1))
            (by rw [Category.assoc, jw_ι, ← Category.assoc, Scheme.homOfLE_ι]) (τ (lam (s.1 1))) =
      (pullbackUnitIso (h.resLE (𝒱.inter t) (𝒲.inter s) hWt)).symm ≪≫
        (Scheme.Modules.pullback (h.resLE (𝒱.inter t) (𝒲.inter s) hWt)).mapIso
          ((τ.restrict (𝒱.inter_le t i₀)).symm ≪≫ τ.restrict (𝒱.inter_le t i₁)) ≪≫
        pullbackUnitIso (h.resLE (𝒱.inter t) (𝒲.inter s) hWt) := by
  have hm : h.resLE (𝒱.inter t) (𝒲.inter s) hWt ≫ (𝒱.inter t).ι = (𝒲.inter s).ι ≫ h :=
    Scheme.Hom.resLE_comp_ι _ _
  have ek : ∀ i, (h.resLE (𝒱.inter t) (𝒲.inter s) hWt ≫ Y.homOfLE (𝒱.inter_le t i)) ≫ (𝒱.U (t.1 i)).ι =
      (𝒲.inter s).ι ≫ h := fun i => by
    rw [Category.assoc, Scheme.homOfLE_ι, hm]
  rw [← genRestrict_chart_congr 𝒱 𝓜 τ h₀ ((𝒲.inter s).ι ≫ h)
      (h.resLE (𝒱.inter t) (𝒲.inter s) hWt ≫ Y.homOfLE (𝒱.inter_le t i₀)) _ (ek i₀),
    ← genRestrict_chart_congr 𝒱 𝓜 τ h₁ ((𝒲.inter s).ι ≫ h)
      (h.resLE (𝒱.inter t) (𝒲.inter s) hWt ≫ Y.homOfLE (𝒱.inter_le t i₁)) _ (ek i₁)]
  rw [genRestrict_comp 𝓜 (𝒱.U (t.1 i₀)).ι (𝒱.inter t).ι (Y.homOfLE (𝒱.inter_le t i₀)) (Y.homOfLE_ι _)
      (τ (t.1 i₀)) (h.resLE (𝒱.inter t) (𝒲.inter s) hWt) ((𝒲.inter s).ι ≫ h) hm _ rfl (ek i₀),
    genRestrict_comp 𝓜 (𝒱.U (t.1 i₁)).ι (𝒱.inter t).ι (Y.homOfLE (𝒱.inter_le t i₁)) (Y.homOfLE_ι _)
      (τ (t.1 i₁)) (h.resLE (𝒱.inter t) (𝒲.inter s) hWt) ((𝒲.inter s).ι ≫ h) hm _ rfl (ek i₁),
    ← restrict_eq_genRestrict, ← restrict_eq_genRestrict]
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Iso.app_hom, Iso.app_inv, Functor.map_comp, Category.assoc]
  erw [Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app_assoc]
  try rfl

theorem clause_Tplus (s : 𝒲.Idx 1) (hinj : Function.Injective (lam ∘ s.1)) (hlt : lam (s.1 0) < lam (s.1 1)) :
    (tauP h 𝒱 𝒲 lam hlam 𝓜 τ).transition s =
      (X.presheaf.map (homOfLE (𝒲.inter_le_preimage_inter_sortIdx h 𝒱 lam hlam s hinj)).op).hom
        ((h.app (𝒱.inter (𝒲.sortIdx 𝒱 lam s hinj))).hom (τ.transition (𝒲.sortIdx 𝒱 lam s hinj))) := by
  obtain ⟨ht0, ht1⟩ := (sortIdx_fin_two h 𝒱 𝒲 lam s hinj).1 hlt
  rw [tauP_transition, symm_trans_eq_conj h 𝒱 𝒲 lam hlam 𝓜 τ s (𝒲.sortIdx 𝒱 lam s hinj)
    (𝒲.inter_le_preimage_inter_sortIdx h 𝒱 lam hlam s hinj) 0 1 ht0 ht1]
  exact (uASm_resLE h (𝒲.inter_le_preimage_inter_sortIdx h 𝒱 lam hlam s hinj) _).symm

theorem clause_Tminus (s : 𝒲.Idx 1) (hinj : Function.Injective (lam ∘ s.1)) (hlt : lam (s.1 1) < lam (s.1 0)) :
    (tauP h 𝒱 𝒲 lam hlam 𝓜 τ).transition s *
      (X.presheaf.map (homOfLE (𝒲.inter_le_preimage_inter_sortIdx h 𝒱 lam hlam s hinj)).op).hom
        ((h.app (𝒱.inter (𝒲.sortIdx 𝒱 lam s hinj))).hom (τ.transition (𝒲.sortIdx 𝒱 lam s hinj))) = 1 := by
  obtain ⟨ht0, ht1⟩ := (sortIdx_fin_two h 𝒱 𝒲 lam s hinj).2 hlt
  rw [tauP_transition, symm_trans_eq_conj h 𝒱 𝒲 lam hlam 𝓜 τ s (𝒲.sortIdx 𝒱 lam s hinj)
    (𝒲.inter_le_preimage_inter_sortIdx h 𝒱 lam hlam s hinj) 1 0 ht1 ht0]
  rw [transition_eq_θ, θ, uASm_resLE h (𝒲.inter_le_preimage_inter_sortIdx h 𝒱 lam hlam s hinj), ← uASm_trans]
  exact uASm_eq_one_of_eq_refl _ _ (conj_trans_conj_eq_refl _ _ _ _)

end main

end PV1TLT1

open PV1TL PV1TLT1 in
theorem solution
    {X Y : Scheme.{u}} (h : X ⟶ Y) (𝒱 : Y.OrderedAffineCover) (𝒲 : X.OrderedAffineCover) (lam : 𝒲.ι → 𝒱.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒱.U (lam w))
    (𝓜 : Y.Modules) (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓜) :
    ∃ τ' : Scheme.Modules.CechTrivialisation 𝒲 ((Scheme.Modules.pullback h).obj 𝓜),

      (∀ w : 𝒲.ι, τ' w =
        ((Scheme.Modules.pullbackComp (𝒲.U w).ι h).app 𝓜) ≪≫
          ((Scheme.Modules.pullbackCongr
              (show (𝒲.U w).ι ≫ h = (X.homOfLE (hlam w) ≫ (h ∣_ 𝒱.U (lam w))) ≫ (𝒱.U (lam w)).ι by
                rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι])).app 𝓜) ≪≫
          ((Scheme.Modules.pullbackComp (X.homOfLE (hlam w) ≫ (h ∣_ 𝒱.U (lam w))) (𝒱.U (lam w)).ι).app 𝓜).symm ≪≫
          (Scheme.Modules.pullback (X.homOfLE (hlam w) ≫ (h ∣_ 𝒱.U (lam w)))).mapIso (τ (lam w)) ≪≫
          Scheme.Modules.pullbackUnitIso (X.homOfLE (hlam w) ≫ (h ∣_ 𝒱.U (lam w)))) ∧

      (∀ s : 𝒲.Idx 1, lam (s.1 0) = lam (s.1 1) → τ'.transition s = 1) ∧

      (∀ (s : 𝒲.Idx 1) (hinj : Function.Injective (lam ∘ s.1)), lam (s.1 0) < lam (s.1 1) →
        τ'.transition s =
          (X.presheaf.map (homOfLE (𝒲.inter_le_preimage_inter_sortIdx h 𝒱 lam hlam s hinj)).op).hom
            ((h.app (𝒱.inter (𝒲.sortIdx 𝒱 lam s hinj))).hom (τ.transition (𝒲.sortIdx 𝒱 lam s hinj)))) ∧

      (∀ (s : 𝒲.Idx 1) (hinj : Function.Injective (lam ∘ s.1)), lam (s.1 1) < lam (s.1 0) →
        τ'.transition s *
          (X.presheaf.map (homOfLE (𝒲.inter_le_preimage_inter_sortIdx h 𝒱 lam hlam s hinj)).op).hom
            ((h.app (𝒱.inter (𝒲.sortIdx 𝒱 lam s hinj))).hom (τ.transition (𝒲.sortIdx 𝒱 lam s hinj))) = 1) := by
  refine ⟨tauP h 𝒱 𝒲 lam hlam 𝓜 τ, fun w => ?_, clause_T0 h 𝒱 𝒲 lam hlam 𝓜 τ,
    clause_Tplus h 𝒱 𝒲 lam hlam 𝓜 τ, clause_Tminus h 𝒱 𝒲 lam hlam 𝓜 τ⟩
  apply Iso.ext
  simp only [tauP, jw, genRestrict, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, pullbackCongr_hom_app_eq, pullbackCongr_inv_app_eq]

end S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_refinement_transition_eq
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_refinement_transition_eq (solution)
