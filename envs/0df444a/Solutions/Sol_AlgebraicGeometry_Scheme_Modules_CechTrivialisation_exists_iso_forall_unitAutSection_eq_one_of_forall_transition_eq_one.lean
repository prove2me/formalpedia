-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.CechTrivialisation.exists_iso_forall_unitAutSection_eq_one_of_forall_transition_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/79214434-4d07-51be-9769-c1cb1b5f2994

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_hom_app_comp_pullbackUnitIso_hom
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_existsUnique_iso_forall_pullback_mapIso_eq_of_iSup_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_iso_forall_unitAutSection_eq_one_of_forall_transition_eq_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace L5G
namespace UA
open AlgebraicGeometry.Scheme.Modules

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

end L5G.UA

open L5G.UA

namespace L5G

section coh

p2m_open "AlgebraicGeometry.Scheme.Modules"

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

end L5G

namespace L5G
p2m_open "AlgebraicGeometry.Scheme.Modules"

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

end L5G

namespace L5G
p2m_open "AlgebraicGeometry.Scheme.Modules"

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

end L5G

namespace L5G
p2m_open "AlgebraicGeometry.Scheme.Modules"

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

end L5G

namespace L5G
p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_iso_forall_unitAutSection_eq_one_of_forall_transition_eq_one.L5G.UA"

variable {Y : Scheme.{u}}

section localAgree
variable (W : Y.Opens)

theorem eq_refl_of_uASm_eq_one
    (E : @Iso ((W : Scheme.{u}).Modules) _ (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)
      (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf))
    (h : uASm W E = 1) : E = Iso.refl _ := by

  have h1 : uapp W E 1 = 1 := by
    rw [uASm_eq] at h
    have h2 := congrArg W.topIso.inv.hom h
    rw [map_one, ← CommRingCat.comp_apply, Iso.hom_inv_id] at h2
    exact h2
  apply Iso.ext

  apply (SheafOfModules.unit ((W : Scheme.{u}).ringCatSheaf)).unitHomEquiv.injective
  apply PresheafOfModules.sections_ext
  intro V
  let f : (op ⊤ : ((W : Scheme.{u}).Opens)ᵒᵖ) ⟶ V := (homOfLE (le_top (a := V.unop))).op
  have H : ∀ (s t : (SheafOfModules.unit ((W : Scheme.{u}).ringCatSheaf)).sections),
      s.val (op ⊤) = t.val (op ⊤) → s.val V = t.val V := by
    intro s t hst
    rw [← PresheafOfModules.sections_property s f, ← PresheafOfModules.sections_property t f, hst]
  apply H
  first
    | exact h1
    | (change uapp W E 1 = uapp W (Iso.refl _) 1
       rw [h1, uapp_refl])
    | (rw [SheafOfModules.unitHomEquiv_apply_coe, SheafOfModules.unitHomEquiv_apply_coe]
       change uapp W E 1 = (1 : (W : Scheme.{u}).presheaf.obj (op ⊤))
       exact h1)

end localAgree

variable {𝒱 : Y.OrderedAffineCover} {𝓜 : Y.Modules} (τ : CechTrivialisation 𝒱 𝓜)

theorem restrict_congr_idx {a a' : 𝒱.ι} (e : a = a') {W : Y.Opens} (ha : W ≤ 𝒱.U a) (ha' : W ≤ 𝒱.U a') :
    τ.restrict ha = τ.restrict ha' := by
  subst e; rfl

def pair {a b : 𝒱.ι} (hab : a < b) : 𝒱.Idx 1 :=
  ⟨![a, b], Fin.strictMono_iff_lt_succ.2 (fun i => by
    fin_cases i
    simpa using hab)⟩

theorem pair_zero {a b : 𝒱.ι} (hab : a < b) : (pair (𝒱 := 𝒱) hab).1 0 = a := rfl
theorem pair_one {a b : 𝒱.ι} (hab : a < b) : (pair (𝒱 := 𝒱) hab).1 1 = b := rfl

theorem le_inter_pair {a b : 𝒱.ι} (hab : a < b) {W : Y.Opens} (ha : W ≤ 𝒱.U a) (hb : W ≤ 𝒱.U b) :
    W ≤ 𝒱.inter (pair hab) := by
  refine le_iInf fun j => ?_
  fin_cases j
  · exact ha
  · exact hb

theorem restrict_eq_of_lt (h1 : ∀ s : 𝒱.Idx 1, τ.transition s = 1)
    {a b : 𝒱.ι} (hab : a < b) {W : Y.Opens} (ha : W ≤ 𝒱.U a) (hb : W ≤ 𝒱.U b) :
    τ.restrict ha = τ.restrict hb := by
  have hW := le_inter_pair hab ha hb
  have key := θ_res τ hW ((pair hab).1 0) ((pair hab).1 1) (𝒱.inter_le _ 0) (𝒱.inter_le _ 1)
  rw [← transition_eq_θ, h1, map_one] at key

  have E := eq_refl_of_uASm_eq_one W _ key.symm

  have E' : τ.restrict (hW.trans (𝒱.inter_le (pair hab) 1)) = τ.restrict (hW.trans (𝒱.inter_le (pair hab) 0)) := by
    calc τ.restrict (hW.trans (𝒱.inter_le (pair hab) 1))
        = τ.restrict (hW.trans (𝒱.inter_le (pair hab) 0)) ≪≫
            ((τ.restrict (hW.trans (𝒱.inter_le (pair hab) 0))).symm ≪≫
              τ.restrict (hW.trans (𝒱.inter_le (pair hab) 1))) := by simp
      _ = τ.restrict (hW.trans (𝒱.inter_le (pair hab) 0)) := by rw [E]; simp
  rw [restrict_congr_idx τ (pair_zero hab) _ ha, restrict_congr_idx τ (pair_one hab) _ hb] at E'
  exact E'.symm

theorem restrict_indep (h1 : ∀ s : 𝒱.Idx 1, τ.transition s = 1)
    {a b : 𝒱.ι} {W : Y.Opens} (ha : W ≤ 𝒱.U a) (hb : W ≤ 𝒱.U b) :
    τ.restrict ha = τ.restrict hb := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · exact restrict_eq_of_lt τ h1 hab ha hb
  · rfl
  · exact (restrict_eq_of_lt τ h1 hba hb ha).symm

theorem mapIso_pullbackUnitIso_trans {W W' : Y.Opens} (h' : W' ≤ W) :
    (Scheme.Modules.pullback (Y.homOfLE h')).mapIso (pullbackUnitIso W.ι) ≪≫ pullbackUnitIso (Y.homOfLE h') =
      κiso (SheafOfModules.unit Y.ringCatSheaf) h' ≪≫ pullbackUnitIso W'.ι := by
  apply Iso.ext
  simp only [Iso.trans_hom, Functor.mapIso_hom, κiso, Iso.app_hom, Category.assoc]
  rw [congr_unit (Y.homOfLE_ι h')]
  exact (Scheme.Modules.pullbackComp_hom_app_comp_pullbackUnitIso_hom (Y.homOfLE h') W.ι).symm

variable (𝒱) in

def Sub : Type u := {W : Y.Opens // ∃ a : 𝒱.ι, W ≤ 𝒱.U a}

noncomputable def ch (i : Sub 𝒱) : 𝒱.ι := i.2.choose

theorem le_ch (i : Sub 𝒱) : i.1 ≤ 𝒱.U (ch i) := i.2.choose_spec

theorem iSup_sub_eq_top : ⨆ i : Sub 𝒱, i.1 = ⊤ := by
  rw [eq_top_iff, ← 𝒱.iSup_eq_top]
  exact iSup_le fun a => le_iSup_of_le (⟨𝒱.U a, a, le_rfl⟩ : Sub 𝒱) le_rfl

theorem sub_basisLike (i j : Sub 𝒱) :
    i.1 ⊓ j.1 ≤ ⨆ (k : {k : Sub 𝒱 // k.1 ≤ i.1 ⊓ j.1}), k.1.1 :=
  le_iSup_of_le (⟨⟨i.1 ⊓ j.1, ch i, inf_le_left.trans (le_ch i)⟩, le_rfl⟩ : {k : Sub 𝒱 // k.1 ≤ i.1 ⊓ j.1})
    le_rfl

noncomputable def eSub (i : Sub 𝒱) :
    (Scheme.Modules.pullback i.1.ι).obj 𝓜 ≅
      (Scheme.Modules.pullback i.1.ι).obj (SheafOfModules.unit Y.ringCatSheaf) :=
  τ.restrict (le_ch i) ≪≫ (pullbackUnitIso i.1.ι).symm

theorem eSub_compat (h1 : ∀ s : 𝒱.Idx 1, τ.transition s = 1) (i j : Sub 𝒱) (h : j.1 ≤ i.1) :
    (Scheme.Modules.pullback (Y.homOfLE h)).mapIso (eSub τ i) =
      ((Scheme.Modules.pullbackComp (Y.homOfLE h) i.1.ι).app 𝓜 ≪≫
          (Scheme.Modules.pullbackCongr (Y.homOfLE_ι h)).app 𝓜) ≪≫
        eSub τ j ≪≫
        ((Scheme.Modules.pullbackComp (Y.homOfLE h) i.1.ι).app (SheafOfModules.unit Y.ringCatSheaf) ≪≫
          (Scheme.Modules.pullbackCongr (Y.homOfLE_ι h)).app (SheafOfModules.unit Y.ringCatSheaf)).symm := by

  have hres : (Scheme.Modules.pullback (Y.homOfLE h)).mapIso (τ.restrict (le_ch i)) =
      κiso 𝓜 h ≪≫ τ.restrict (le_ch j) ≪≫ (pullbackUnitIso (Y.homOfLE h)).symm := by
    rw [← restrict_indep τ h1 (h.trans (le_ch i)) (le_ch j), restrict_trans τ (le_ch i) h]
    simp
  have hunit : (Scheme.Modules.pullback (Y.homOfLE h)).mapIso ((pullbackUnitIso i.1.ι).symm) =
      pullbackUnitIso (Y.homOfLE h) ≪≫ (pullbackUnitIso j.1.ι).symm ≪≫
        (κiso (SheafOfModules.unit Y.ringCatSheaf) h).symm := by
    have e := mapIso_pullbackUnitIso_trans (Y := Y) h
    rw [Functor.mapIso_symm]
    calc ((Scheme.Modules.pullback (Y.homOfLE h)).mapIso (pullbackUnitIso i.1.ι)).symm
        = ((Scheme.Modules.pullback (Y.homOfLE h)).mapIso (pullbackUnitIso i.1.ι) ≪≫
            pullbackUnitIso (Y.homOfLE h) ≪≫ (pullbackUnitIso (Y.homOfLE h)).symm).symm := by simp
      _ = ((κiso (SheafOfModules.unit Y.ringCatSheaf) h ≪≫ pullbackUnitIso j.1.ι) ≪≫
            (pullbackUnitIso (Y.homOfLE h)).symm).symm := by rw [← Iso.trans_assoc, e]
      _ = _ := by simp
  change (Scheme.Modules.pullback (Y.homOfLE h)).mapIso (τ.restrict (le_ch i) ≪≫ (pullbackUnitIso i.1.ι).symm) =
    κiso 𝓜 h ≪≫ (τ.restrict (le_ch j) ≪≫ (pullbackUnitIso j.1.ι).symm) ≪≫
      (κiso (SheafOfModules.unit Y.ringCatSheaf) h).symm
  rw [Functor.mapIso_trans, hres, hunit]
  simp

theorem main (h1 : ∀ s : 𝒱.Idx 1, τ.transition s = 1) :
    Nonempty (𝓜 ≅ SheafOfModules.unit Y.ringCatSheaf) := by
  obtain ⟨f, -, -⟩ :=
    Scheme.Modules.existsUnique_iso_forall_pullback_mapIso_eq_of_iSup_eq_top 𝓜
      (SheafOfModules.unit Y.ringCatSheaf) (fun i : Sub 𝒱 => i.1) iSup_sub_eq_top sub_basisLike
      (eSub τ) (eSub_compat τ h1)
  exact ⟨f⟩

section restrictRefl
variable {V : Scheme.{u}}

theorem pullbackUnitIso_id (X : Scheme.{u}) :
    (pullbackUnitIso (𝟙 X)).hom = (pullbackId X).hom.app (SheafOfModules.unit X.ringCatSheaf) := by
  apply ((pullbackPushforwardAdjunction (𝟙 X)).homEquiv _ _).injective
  have h1 : (pullbackPushforwardAdjunction (𝟙 X)).homEquiv (SheafOfModules.unit X.ringCatSheaf)
      (SheafOfModules.unit X.ringCatSheaf) (pullbackUnitIso (𝟙 X)).hom =
      SheafOfModules.unitToPushforwardObjUnit (𝟙 X : X ⟶ X).toRingCatSheafHom := by
    have e0 : (pullbackUnitIso (𝟙 X)).hom = ((pullbackPushforwardAdjunction (𝟙 X)).homEquiv _ _).symm
        (SheafOfModules.unitToPushforwardObjUnit (𝟙 X : X ⟶ X).toRingCatSheafHom) := rfl
    rw [e0, Equiv.apply_symm_apply]
  have h2 : (pullbackPushforwardAdjunction (𝟙 X)).homEquiv (SheafOfModules.unit X.ringCatSheaf)
      (SheafOfModules.unit X.ringCatSheaf) ((pullbackId X).hom.app (SheafOfModules.unit X.ringCatSheaf)) =
      (pushforwardId X).inv.app (SheafOfModules.unit X.ringCatSheaf) := by
    have key := unit_conjugateEquiv Adjunction.id (pullbackPushforwardAdjunction (𝟙 X)) (pullbackId X).hom
      (SheafOfModules.unit X.ringCatSheaf)
    rw [Scheme.Modules.conjugateEquiv_pullbackId_hom] at key
    erw [Adjunction.homEquiv_unit, ← key]
    simp
  rw [h1, h2]
  apply Scheme.Modules.hom_ext
  intro U
  erw [Scheme.Modules.pushforwardId_inv_app_app]

theorem genRestrict_id (𝓜 : Y.Modules) (ι : V ⟶ Y) (e : 𝟙 V ≫ ι = ι)
    (τa : (Scheme.Modules.pullback ι).obj 𝓜 ≅ SheafOfModules.unit V.ringCatSheaf) :
    genRestrict 𝓜 ι ι (𝟙 V) e τa = τa := by
  have ru := NatTrans.congr_app (pseudofunctor_right_unitality ι) 𝓜
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, eqToHom_app] at ru
  apply Iso.ext
  simp only [genRestrict, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom, pullbackCongr_inv_app_eq,
    pullbackUnitIso_id]
  erw [(pullbackId V).hom.naturality τa.hom]
  erw [Functor.id_map]
  erw [reassoc_of% ru]
  rfl

variable {𝒱 : Y.OrderedAffineCover} {𝓜 : Y.Modules} (τ : CechTrivialisation 𝒱 𝓜)

theorem genRestrict_congr_k (𝓜 : Y.Modules) (ι : V ⟶ Y) {B : Scheme.{u}} (j : B ⟶ Y) {k k' : B ⟶ V} (hk : k = k')
    (e : k ≫ ι = j) (e' : k' ≫ ι = j) (τa : (Scheme.Modules.pullback ι).obj 𝓜 ≅ SheafOfModules.unit V.ringCatSheaf) :
    genRestrict 𝓜 ι j k e τa = genRestrict 𝓜 ι j k' e' τa := by
  subst hk; rfl

theorem restrict_refl (a : 𝒱.ι) : τ.restrict (le_refl (𝒱.U a)) = τ a := by
  rw [restrict_eq_genRestrict,
    genRestrict_congr_k 𝓜 (𝒱.U a).ι (𝒱.U a).ι (Scheme.homOfLE_rfl Y (𝒱.U a)) _ (Category.id_comp _) (τ a)]
  exact genRestrict_id 𝓜 (𝒱.U a).ι _ (τ a)

end restrictRefl

variable {𝒱 : Y.OrderedAffineCover} {𝓜 : Y.Modules} (τ : CechTrivialisation 𝒱 𝓜) in

theorem main_charts (h1 : ∀ s : 𝒱.Idx 1, τ.transition s = 1) :
    ∃ φ : 𝓜 ≅ SheafOfModules.unit Y.ringCatSheaf, ∀ a : 𝒱.ι,
      unitAutSection (𝒱.U a)
        ((τ a).symm ≪≫ (Scheme.Modules.pullback (𝒱.U a).ι).mapIso φ ≪≫ pullbackUnitIso (𝒱.U a).ι) = 1 := by
  obtain ⟨f, hf, -⟩ :=
    Scheme.Modules.existsUnique_iso_forall_pullback_mapIso_eq_of_iSup_eq_top 𝓜
      (SheafOfModules.unit Y.ringCatSheaf) (fun i : Sub 𝒱 => i.1) iSup_sub_eq_top sub_basisLike
      (eSub τ) (eSub_compat τ h1)
  refine ⟨f, fun a => ?_⟩
  have hfa := hf ⟨𝒱.U a, a, le_rfl⟩
  change (Scheme.Modules.pullback (𝒱.U a).ι).mapIso f =
    τ.restrict (le_ch (⟨𝒱.U a, a, le_rfl⟩ : Sub 𝒱)) ≪≫ (pullbackUnitIso (𝒱.U a).ι).symm at hfa
  rw [restrict_indep τ h1 (le_ch (⟨𝒱.U a, a, le_rfl⟩ : Sub 𝒱)) (le_refl _), restrict_refl] at hfa
  rw [hfa]
  have key : ((τ a).symm ≪≫ (τ a ≪≫ (pullbackUnitIso (𝒱.U a).ι).symm)) ≪≫ pullbackUnitIso (𝒱.U a).ι =
      Iso.refl _ := by
    apply Iso.ext
    simp
  exact (congrArg (unitAutSection (𝒱.U a)) key).trans (unitAutSection_refl _)

end L5G

theorem solution
    {Y : Scheme.{u}} {𝒱 : Y.OrderedAffineCover} {𝓜 : Y.Modules}
    (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓜)
    (h : ∀ s : 𝒱.Idx 1, τ.transition s = 1) :
    ∃ φ : 𝓜 ≅ SheafOfModules.unit Y.ringCatSheaf, ∀ a : 𝒱.ι,
      Scheme.Modules.unitAutSection (𝒱.U a)
        ((τ a).symm ≪≫ (Scheme.Modules.pullback (𝒱.U a).ι).mapIso φ ≪≫
          Scheme.Modules.pullbackUnitIso (𝒱.U a).ι) = 1 := by
  exact L5G.main_charts τ h

end S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_iso_forall_unitAutSection_eq_one_of_forall_transition_eq_one
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_iso_forall_unitAutSection_eq_one_of_forall_transition_eq_one (solution)
