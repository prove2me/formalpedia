-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_forall_pullback_iso_of_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/32cf0310-6d1c-510a-9a91-a6aa405464d9

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_toDescentData_essSurj_of_openCover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_forall_pullback_iso_of_cocycle

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace MZG

noncomputable abbrev Mdl : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat :=
  (AlgebraicGeometry.Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁

theorem Mdl_keyMC {a b d : LocallyDiscrete Scheme.{u}ᵒᵖ} (u' : a ⟶ b) (v' : b ⟶ d) (M : Mdl.obj a) :
    (Mdl.mapComp' u' v' (u' ≫ v') rfl).hom.toNatTrans.app M = (Mdl.mapComp u' v').hom.toNatTrans.app M := by
  rw [Pseudofunctor.mapComp'_eq_mapComp]

theorem Mdl_keyMC_inv {a b d : LocallyDiscrete Scheme.{u}ᵒᵖ} (u' : a ⟶ b) (v' : b ⟶ d) (M : Mdl.obj a) :
    (Mdl.mapComp' u' v' (u' ≫ v') rfl).inv.toNatTrans.app M = (Mdl.mapComp u' v').inv.toNatTrans.app M := by
  rw [Pseudofunctor.mapComp'_eq_mapComp]

theorem Mdl_mapComp'_hom_app {X₀ X₁ Y : Scheme.{u}} (f : X₀ ⟶ X₁) (g : X₁ ⟶ Y) (L : Y.Modules)
    (fg : X₀ ⟶ Y) (hfg : f ≫ g = fg) :
    (Mdl.mapComp' g.op.toLoc f.op.toLoc fg.op.toLoc (by rw [← hfg]; rfl)).hom.toNatTrans.app L =
    (Scheme.Modules.pullbackCongr hfg.symm).hom.app L ≫ (Scheme.Modules.pullbackComp f g).inv.app L := by
  subst hfg
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  exact Mdl_keyMC g.op.toLoc f.op.toLoc L

theorem Mdl_mapComp'_inv_app {X₀ X₁ Y : Scheme.{u}} (f : X₀ ⟶ X₁) (g : X₁ ⟶ Y) (L : Y.Modules)
    (fg : X₀ ⟶ Y) (hfg : f ≫ g = fg) :
    (Mdl.mapComp' g.op.toLoc f.op.toLoc fg.op.toLoc (by rw [← hfg]; rfl)).inv.toNatTrans.app L =
    (Scheme.Modules.pullbackComp f g).hom.app L ≫ (Scheme.Modules.pullbackCongr hfg).hom.app L := by
  subst hfg
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id]
  exact Mdl_keyMC_inv g.op.toLoc f.op.toLoc L

theorem pullHom_eq {Z' Z X₁ X₂ : Scheme.{u}} (e : Z' ⟶ Z) (f₁ : Z ⟶ X₁) (f₂ : Z ⟶ X₂)
    (M₁ : X₁.Modules) (M₂ : X₂.Modules)
    (φ : (Scheme.Modules.pullback f₁).obj M₁ ⟶ (Scheme.Modules.pullback f₂).obj M₂) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := Mdl)
        (X₁ := X₁) (X₂ := X₂) (M₁ := M₁) (M₂ := M₂) (f₁ := f₁) (f₂ := f₂) φ e (e ≫ f₁) (e ≫ f₂) rfl rfl =
      (Scheme.Modules.pullbackComp e f₁).inv.app M₁ ≫ (Scheme.Modules.pullback e).map φ ≫
        (Scheme.Modules.pullbackComp e f₂).hom.app M₂ := by
  dsimp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  rw [Mdl_mapComp'_hom_app e f₁ M₁ (e ≫ f₁) rfl, Mdl_mapComp'_inv_app e f₂ M₂ (e ≫ f₂) rfl]
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    Category.comp_id]
  rfl

theorem pullHom_transport {Z' Z X₁ X₂ : Scheme.{u}} (e : Z' ⟶ Z) (f₁ : Z ⟶ X₁) (f₂ : Z ⟶ X₂)
    (M₁ : X₁.Modules) (M₂ : X₂.Modules)
    (φ : (Scheme.Modules.pullback f₁).obj M₁ ⟶ (Scheme.Modules.pullback f₂).obj M₂)
    (a : Z' ⟶ X₁) (b : Z' ⟶ X₂) (ha : e ≫ f₁ = a) (hb : e ≫ f₂ = b) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := Mdl)
        (X₁ := X₁) (X₂ := X₂) (M₁ := M₁) (M₂ := M₂) (f₁ := f₁) (f₂ := f₂) φ e a b ha hb =
      eqToHom (congrArg (fun k => (Scheme.Modules.pullback k).obj M₁) ha.symm) ≫
      ((Scheme.Modules.pullbackComp e f₁).inv.app M₁ ≫ (Scheme.Modules.pullback e).map φ ≫
        (Scheme.Modules.pullbackComp e f₂).hom.app M₂) ≫
      eqToHom (congrArg (fun k => (Scheme.Modules.pullback k).obj M₂) hb) := by
  subst ha hb
  rw [pullHom_eq]
  simp

theorem pullHom_congr {Z' Z X₁ X₂ : Scheme.{u}} {e e' : Z' ⟶ Z} (he : e = e') (f₁ : Z ⟶ X₁) (f₂ : Z ⟶ X₂)
    (M₁ : X₁.Modules) (M₂ : X₂.Modules)
    (φ : (Scheme.Modules.pullback f₁).obj M₁ ⟶ (Scheme.Modules.pullback f₂).obj M₂)
    (a : Z' ⟶ X₁) (b : Z' ⟶ X₂) (ha : e ≫ f₁ = a) (hb : e ≫ f₂ = b) (ha' : e' ≫ f₁ = a) (hb' : e' ≫ f₂ = b) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := Mdl)
        (X₁ := X₁) (X₂ := X₂) (M₁ := M₁) (M₂ := M₂) (f₁ := f₁) (f₂ := f₂) φ e a b ha hb =
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := Mdl)
        (X₁ := X₁) (X₂ := X₂) (M₁ := M₁) (M₂ := M₂) (f₁ := f₁) (f₂ := f₂) φ e' a b ha' hb' := by
  subst he; rfl

theorem pullbackCongr_hom_app {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr h).hom.app M = eqToHom (congrArg (fun k => (Scheme.Modules.pullback k).obj M) h) := by
  subst h; simp [Scheme.Modules.pullbackCongr]

theorem pullbackCongr_inv_app {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr h).inv.app M = eqToHom (congrArg (fun k => (Scheme.Modules.pullback k).obj M) h.symm) := by
  subst h; simp [Scheme.Modules.pullbackCongr]

section Datum

variable {Y : Scheme.{u}} {I : Type u} {X : I → Scheme.{u}} (ι : ∀ i, X i ⟶ Y)
  (M : ∀ i, (X i).Modules)
  (φ : ∀ i j : I,
      (Scheme.Modules.pullback (Limits.pullback.fst (ι i) (ι j))).obj (M i) ≅
        (Scheme.Modules.pullback (Limits.pullback.snd (ι i) (ι j))).obj (M j))

noncomputable def homD (i₁ i₂ : I) {T : Scheme.{u}} (f₁ : T ⟶ X i₁) (f₂ : T ⟶ X i₂) (w : f₁ ≫ ι i₁ = f₂ ≫ ι i₂) :
    (Scheme.Modules.pullback f₁).obj (M i₁) ⟶ (Scheme.Modules.pullback f₂).obj (M i₂) :=
  Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := Mdl) (X₁ := X i₁) (X₂ := X i₂) (M₁ := M i₁) (M₂ := M i₂)
    (f₁ := Limits.pullback.fst (ι i₁) (ι i₂)) (f₂ := Limits.pullback.snd (ι i₁) (ι i₂)) (φ i₁ i₂).hom
    (Limits.pullback.lift f₁ f₂ w) f₁ f₂ (Limits.pullback.lift_fst _ _ _) (Limits.pullback.lift_snd _ _ _)

theorem homD_pullHom (i₁ i₂ : I) {T T' : Scheme.{u}} (f₁ : T ⟶ X i₁) (f₂ : T ⟶ X i₂) (w : f₁ ≫ ι i₁ = f₂ ≫ ι i₂)
    (g : T' ⟶ T) (gf₁ : T' ⟶ X i₁) (gf₂ : T' ⟶ X i₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)
    (w' : gf₁ ≫ ι i₁ = gf₂ ≫ ι i₂) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := Mdl) (X₁ := X i₁) (X₂ := X i₂) (M₁ := M i₁) (M₂ := M i₂)
      (f₁ := f₁) (f₂ := f₂) (homD ι M φ i₁ i₂ f₁ f₂ w) g gf₁ gf₂ hgf₁ hgf₂ = homD ι M φ i₁ i₂ gf₁ gf₂ w' := by
  unfold homD
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom_pullHom]
  apply pullHom_congr
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, Limits.pullback.lift_fst, Limits.pullback.lift_fst, hgf₁]
  · rw [Category.assoc, Limits.pullback.lift_snd, Limits.pullback.lift_snd, hgf₂]

noncomputable def ΘIso (i j : I) {T : Scheme.{u}} (π : T ⟶ Limits.pullback (ι i) (ι j)) :
    (Scheme.Modules.pullback (π ≫ Limits.pullback.fst (ι i) (ι j))).obj (M i) ≅
      (Scheme.Modules.pullback (π ≫ Limits.pullback.snd (ι i) (ι j))).obj (M j) :=
  ((Scheme.Modules.pullbackComp π (Limits.pullback.fst (ι i) (ι j))).app (M i)).symm ≪≫
    (Scheme.Modules.pullback π).mapIso (φ i j) ≪≫
    (Scheme.Modules.pullbackComp π (Limits.pullback.snd (ι i) (ι j))).app (M j)

noncomputable def Θ (i j : I) {T : Scheme.{u}} (π : T ⟶ Limits.pullback (ι i) (ι j)) :
    (Scheme.Modules.pullback (π ≫ Limits.pullback.fst (ι i) (ι j))).obj (M i) ⟶
      (Scheme.Modules.pullback (π ≫ Limits.pullback.snd (ι i) (ι j))).obj (M j) :=
  (ΘIso ι M φ i j π).hom

theorem Θ_def (i j : I) {T : Scheme.{u}} (π : T ⟶ Limits.pullback (ι i) (ι j)) :
    Θ ι M φ i j π =
      (Scheme.Modules.pullbackComp π (Limits.pullback.fst (ι i) (ι j))).inv.app (M i) ≫
        (Scheme.Modules.pullback π).map (φ i j).hom ≫
        (Scheme.Modules.pullbackComp π (Limits.pullback.snd (ι i) (ι j))).hom.app (M j) := rfl

theorem Θ_eq_pullHom (i j : I) {T : Scheme.{u}} (π : T ⟶ Limits.pullback (ι i) (ι j)) :
    Θ ι M φ i j π =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := Mdl) (X₁ := X i) (X₂ := X j) (M₁ := M i) (M₂ := M j)
        (f₁ := Limits.pullback.fst (ι i) (ι j)) (f₂ := Limits.pullback.snd (ι i) (ι j)) (φ i j).hom
        π (π ≫ Limits.pullback.fst (ι i) (ι j)) (π ≫ Limits.pullback.snd (ι i) (ι j)) rfl rfl := by
  rw [pullHom_eq, Θ_def]

scoped instance (i j : I) {T : Scheme.{u}} (π : T ⟶ Limits.pullback (ι i) (ι j)) : IsIso (Θ ι M φ i j π) :=
  (ΘIso ι M φ i j π).isIso_hom

theorem homD_eq (i₁ i₂ : I) {T : Scheme.{u}} (f₁ : T ⟶ X i₁) (f₂ : T ⟶ X i₂) (w : f₁ ≫ ι i₁ = f₂ ≫ ι i₂) :
    homD ι M φ i₁ i₂ f₁ f₂ w =
      eqToHom (congrArg (fun k => (Scheme.Modules.pullback k).obj (M i₁)) (Limits.pullback.lift_fst f₁ f₂ w).symm) ≫
        Θ ι M φ i₁ i₂ (Limits.pullback.lift f₁ f₂ w) ≫
        eqToHom (congrArg (fun k => (Scheme.Modules.pullback k).obj (M i₂)) (Limits.pullback.lift_snd f₁ f₂ w)) := by
  unfold homD
  rw [pullHom_transport, Θ_def]

def Cocycle : Prop :=
  ∀ (i j l : I) (T : Scheme.{u})
      (π₁₂ : T ⟶ Limits.pullback (ι i) (ι j)) (π₂₃ : T ⟶ Limits.pullback (ι j) (ι l)) (π₁₃ : T ⟶ Limits.pullback (ι i) (ι l))
      (h₂ : π₁₂ ≫ Limits.pullback.snd (ι i) (ι j) = π₂₃ ≫ Limits.pullback.fst (ι j) (ι l))
      (h₁ : π₁₃ ≫ Limits.pullback.fst (ι i) (ι l) = π₁₂ ≫ Limits.pullback.fst (ι i) (ι j))
      (h₃ : π₁₃ ≫ Limits.pullback.snd (ι i) (ι l) = π₂₃ ≫ Limits.pullback.snd (ι j) (ι l)),
      ((Scheme.Modules.pullbackComp π₁₂ (Limits.pullback.fst (ι i) (ι j))).app (M i)).symm ≪≫
          (Scheme.Modules.pullback π₁₂).mapIso (φ i j) ≪≫
          (Scheme.Modules.pullbackComp π₁₂ (Limits.pullback.snd (ι i) (ι j))).app (M j) ≪≫
          (Scheme.Modules.pullbackCongr h₂).app (M j) ≪≫
          ((Scheme.Modules.pullbackComp π₂₃ (Limits.pullback.fst (ι j) (ι l))).app (M j)).symm ≪≫
          (Scheme.Modules.pullback π₂₃).mapIso (φ j l) ≪≫
          (Scheme.Modules.pullbackComp π₂₃ (Limits.pullback.snd (ι j) (ι l))).app (M l) ≪≫
          (Scheme.Modules.pullbackCongr h₃.symm).app (M l)
        = (Scheme.Modules.pullbackCongr h₁.symm).app (M i) ≪≫
          ((Scheme.Modules.pullbackComp π₁₃ (Limits.pullback.fst (ι i) (ι l))).app (M i)).symm ≪≫
          (Scheme.Modules.pullback π₁₃).mapIso (φ i l) ≪≫
          (Scheme.Modules.pullbackComp π₁₃ (Limits.pullback.snd (ι i) (ι l))).app (M l)

theorem cocycle_hom (hc : Cocycle ι M φ) (i j l : I) (T : Scheme.{u})
    (π₁₂ : T ⟶ Limits.pullback (ι i) (ι j)) (π₂₃ : T ⟶ Limits.pullback (ι j) (ι l)) (π₁₃ : T ⟶ Limits.pullback (ι i) (ι l))
    (h₂ : π₁₂ ≫ Limits.pullback.snd (ι i) (ι j) = π₂₃ ≫ Limits.pullback.fst (ι j) (ι l))
    (h₁ : π₁₃ ≫ Limits.pullback.fst (ι i) (ι l) = π₁₂ ≫ Limits.pullback.fst (ι i) (ι j))
    (h₃ : π₁₃ ≫ Limits.pullback.snd (ι i) (ι l) = π₂₃ ≫ Limits.pullback.snd (ι j) (ι l)) :
    Θ ι M φ i j π₁₂ ≫ eqToHom (congrArg (fun k => (Scheme.Modules.pullback k).obj (M j)) h₂) ≫
      Θ ι M φ j l π₂₃ ≫ eqToHom (congrArg (fun k => (Scheme.Modules.pullback k).obj (M l)) h₃.symm) =
    eqToHom (congrArg (fun k => (Scheme.Modules.pullback k).obj (M i)) h₁.symm) ≫ Θ ι M φ i l π₁₃ := by
  have h := congrArg Iso.hom (hc i j l T π₁₂ π₂₃ π₁₃ h₂ h₁ h₃)
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv,
    pullbackCongr_hom_app] at h
  simp only [Θ_def, Category.assoc]
  exact h

end Datum

end MZG
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_forall_pullback_iso_of_cocycle.MZG"

namespace MZG

section Datum2

variable {Y : Scheme.{u}} {I : Type u} {X : I → Scheme.{u}} (ι : ∀ i, X i ⟶ Y)
  (M : ∀ i, (X i).Modules)
  (φ : ∀ i j : I,
      (Scheme.Modules.pullback (Limits.pullback.fst (ι i) (ι j))).obj (M i) ≅
        (Scheme.Modules.pullback (Limits.pullback.snd (ι i) (ι j))).obj (M j))

theorem homD_self (hc : Cocycle ι M φ) (i : I) {T : Scheme.{u}} (g : T ⟶ X i) (w : g ≫ ι i = g ≫ ι i) :
    homD ι M φ i i g g w = 𝟙 _ := by
  rw [homD_eq]
  have e₁ : Limits.pullback.lift g g w ≫ Limits.pullback.fst (ι i) (ι i) = g := Limits.pullback.lift_fst _ _ _
  have e₂ : Limits.pullback.lift g g w ≫ Limits.pullback.snd (ι i) (ι i) = g := Limits.pullback.lift_snd _ _ _
  have h₂ : Limits.pullback.lift g g w ≫ Limits.pullback.snd (ι i) (ι i) =
      Limits.pullback.lift g g w ≫ Limits.pullback.fst (ι i) (ι i) := e₂.trans e₁.symm
  have hc' := cocycle_hom ι M φ hc i i i T (Limits.pullback.lift g g w) (Limits.pullback.lift g g w)
    (Limits.pullback.lift g g w) h₂ rfl rfl
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at hc'
  have hA : Θ ι M φ i i (Limits.pullback.lift g g w) ≫
      eqToHom (congrArg (fun k => (Scheme.Modules.pullback k).obj (M i)) h₂) = 𝟙 _ := by
    rw [← cancel_mono (Θ ι M φ i i (Limits.pullback.lift g g w)), Category.assoc, Category.id_comp]
    exact hc'
  have split : eqToHom (congrArg (fun k => (Scheme.Modules.pullback k).obj (M i)) e₂) =
      eqToHom (congrArg (fun k => (Scheme.Modules.pullback k).obj (M i)) h₂) ≫
      eqToHom (congrArg (fun k => (Scheme.Modules.pullback k).obj (M i)) e₁) := by
    rw [eqToHom_trans]
  rw [split, ← Category.assoc (Θ ι M φ i i _), hA, Category.id_comp, eqToHom_trans, eqToHom_refl]

theorem homD_comp (hc : Cocycle ι M φ) {i₁ i₂ i₃ : I} {T : Scheme.{u}} (f₁ : T ⟶ X i₁) (f₂ : T ⟶ X i₂) (f₃ : T ⟶ X i₃)
    (w₁₂ : f₁ ≫ ι i₁ = f₂ ≫ ι i₂) (w₂₃ : f₂ ≫ ι i₂ = f₃ ≫ ι i₃) (w₁₃ : f₁ ≫ ι i₁ = f₃ ≫ ι i₃) :
    homD ι M φ i₁ i₂ f₁ f₂ w₁₂ ≫ homD ι M φ i₂ i₃ f₂ f₃ w₂₃ = homD ι M φ i₁ i₃ f₁ f₃ w₁₃ := by
  rw [homD_eq, homD_eq, homD_eq]
  have a₁ : Limits.pullback.lift f₁ f₂ w₁₂ ≫ Limits.pullback.fst (ι i₁) (ι i₂) = f₁ := Limits.pullback.lift_fst _ _ _
  have a₂ : Limits.pullback.lift f₁ f₂ w₁₂ ≫ Limits.pullback.snd (ι i₁) (ι i₂) = f₂ := Limits.pullback.lift_snd _ _ _
  have b₁ : Limits.pullback.lift f₂ f₃ w₂₃ ≫ Limits.pullback.fst (ι i₂) (ι i₃) = f₂ := Limits.pullback.lift_fst _ _ _
  have b₂ : Limits.pullback.lift f₂ f₃ w₂₃ ≫ Limits.pullback.snd (ι i₂) (ι i₃) = f₃ := Limits.pullback.lift_snd _ _ _
  have c₁ : Limits.pullback.lift f₁ f₃ w₁₃ ≫ Limits.pullback.fst (ι i₁) (ι i₃) = f₁ := Limits.pullback.lift_fst _ _ _
  have c₂ : Limits.pullback.lift f₁ f₃ w₁₃ ≫ Limits.pullback.snd (ι i₁) (ι i₃) = f₃ := Limits.pullback.lift_snd _ _ _
  have hc' := cocycle_hom ι M φ hc i₁ i₂ i₃ T (Limits.pullback.lift f₁ f₂ w₁₂) (Limits.pullback.lift f₂ f₃ w₂₃)
    (Limits.pullback.lift f₁ f₃ w₁₃) (a₂.trans b₁.symm) (c₁.trans a₁.symm) (c₂.trans b₂.symm)
  have key : Θ ι M φ i₁ i₂ (Limits.pullback.lift f₁ f₂ w₁₂) ≫
      eqToHom (congrArg (fun k => (Scheme.Modules.pullback k).obj (M i₂)) (a₂.trans b₁.symm)) ≫
      Θ ι M φ i₂ i₃ (Limits.pullback.lift f₂ f₃ w₂₃) =
      eqToHom (congrArg (fun k => (Scheme.Modules.pullback k).obj (M i₁)) (c₁.trans a₁.symm).symm) ≫
      Θ ι M φ i₁ i₃ (Limits.pullback.lift f₁ f₃ w₁₃) ≫
      eqToHom (congrArg (fun k => (Scheme.Modules.pullback k).obj (M i₃)) (c₂.trans b₂.symm)) := by
    have := hc' =≫ eqToHom (congrArg (fun k => (Scheme.Modules.pullback k).obj (M i₃)) (c₂.trans b₂.symm))
    simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using this
  simp only [Category.assoc]
  rw [eqToHom_trans_assoc, reassoc_of% key]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

theorem homD_fst_snd (i j : I) (w : Limits.pullback.fst (ι i) (ι j) ≫ ι i = Limits.pullback.snd (ι i) (ι j) ≫ ι j) :
    homD ι M φ i j (Limits.pullback.fst (ι i) (ι j)) (Limits.pullback.snd (ι i) (ι j)) w = (φ i j).hom := by
  unfold homD
  have h1 : Limits.pullback.lift (Limits.pullback.fst (ι i) (ι j)) (Limits.pullback.snd (ι i) (ι j)) w = 𝟙 _ := by
    apply Limits.pullback.hom_ext <;> simp
  rw [pullHom_congr h1 _ _ _ _ _ _ _ _ _ (Category.id_comp _) (Category.id_comp _)]
  exact Pseudofunctor.LocallyDiscreteOpToCat.pullHom_id _

noncomputable def datum (hc : Cocycle ι M φ) : (Mdl.{u}).DescentData ι where
  obj := M
  hom T q i₁ i₂ f₁ f₂ hf₁ hf₂ := homD ι M φ i₁ i₂ f₁ f₂ (hf₁.trans hf₂.symm)
  pullHom_hom T' T g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ :=
    homD_pullHom ι M φ i₁ i₂ f₁ f₂ _ g gf₁ gf₂ hgf₁ hgf₂ _
  hom_self T q i g hg := homD_self ι M φ hc i g _
  hom_comp T q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := homD_comp ι M φ hc f₁ f₂ f₃ _ _ _

theorem ofObj_hom_eq (Mg : Y.Modules) ⦃Z : Scheme.{u}⦄ (q : Z ⟶ Y) ⦃i j : I⦄ (f₁ : Z ⟶ X i) (f₂ : Z ⟶ X j)
    (hf₁ : f₁ ≫ ι i = q) (hf₂ : f₂ ≫ ι j = q) :
    ((Mdl.toDescentData ι).obj Mg).hom q f₁ f₂ hf₁ hf₂ =
      ((Scheme.Modules.pullbackComp f₁ (ι i)).hom.app Mg ≫ (Scheme.Modules.pullbackCongr hf₁).hom.app Mg) ≫
        (Scheme.Modules.pullbackCongr hf₂.symm).hom.app Mg ≫ (Scheme.Modules.pullbackComp f₂ (ι j)).inv.app Mg := by
  rw [← Mdl_mapComp'_inv_app f₁ (ι i) Mg q hf₁, ← Mdl_mapComp'_hom_app f₂ (ι j) Mg q hf₂]
  rfl

end Datum2
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_forall_pullback_iso_of_cocycle.MZG"

end MZG
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_forall_pullback_iso_of_cocycle.MZG"

open MZG in
theorem solution
    {Y : Scheme.{u}} {I : Type u} {X : I → Scheme.{u}} (ι : ∀ i, X i ⟶ Y) [∀ i, IsOpenImmersion (ι i)]
    (hι : ∀ y : ↥Y, ∃ (i : I) (x : ↥(X i)), (ι i).base x = y)
    (M : ∀ i, (X i).Modules)
    (φ : ∀ i j : I,
      (Scheme.Modules.pullback (Limits.pullback.fst (ι i) (ι j))).obj (M i) ≅
        (Scheme.Modules.pullback (Limits.pullback.snd (ι i) (ι j))).obj (M j))
    (hcocycle : ∀ (i j l : I) (T : Scheme.{u})
      (π₁₂ : T ⟶ Limits.pullback (ι i) (ι j)) (π₂₃ : T ⟶ Limits.pullback (ι j) (ι l)) (π₁₃ : T ⟶ Limits.pullback (ι i) (ι l))
      (h₂ : π₁₂ ≫ Limits.pullback.snd (ι i) (ι j) = π₂₃ ≫ Limits.pullback.fst (ι j) (ι l))
      (h₁ : π₁₃ ≫ Limits.pullback.fst (ι i) (ι l) = π₁₂ ≫ Limits.pullback.fst (ι i) (ι j))
      (h₃ : π₁₃ ≫ Limits.pullback.snd (ι i) (ι l) = π₂₃ ≫ Limits.pullback.snd (ι j) (ι l)),

      ((Scheme.Modules.pullbackComp π₁₂ (Limits.pullback.fst (ι i) (ι j))).app (M i)).symm ≪≫
          (Scheme.Modules.pullback π₁₂).mapIso (φ i j) ≪≫
          (Scheme.Modules.pullbackComp π₁₂ (Limits.pullback.snd (ι i) (ι j))).app (M j) ≪≫
          (Scheme.Modules.pullbackCongr h₂).app (M j) ≪≫
          ((Scheme.Modules.pullbackComp π₂₃ (Limits.pullback.fst (ι j) (ι l))).app (M j)).symm ≪≫
          (Scheme.Modules.pullback π₂₃).mapIso (φ j l) ≪≫
          (Scheme.Modules.pullbackComp π₂₃ (Limits.pullback.snd (ι j) (ι l))).app (M l) ≪≫
          (Scheme.Modules.pullbackCongr h₃.symm).app (M l)
        = (Scheme.Modules.pullbackCongr h₁.symm).app (M i) ≪≫
          ((Scheme.Modules.pullbackComp π₁₃ (Limits.pullback.fst (ι i) (ι l))).app (M i)).symm ≪≫
          (Scheme.Modules.pullback π₁₃).mapIso (φ i l) ≪≫
          (Scheme.Modules.pullbackComp π₁₃ (Limits.pullback.snd (ι i) (ι l))).app (M l)) :
    ∃ (Mg : Y.Modules) (ψ : ∀ i, (Scheme.Modules.pullback (ι i)).obj Mg ≅ M i),
      ∀ i j : I,
        ((Scheme.Modules.pullbackComp (Limits.pullback.fst (ι i) (ι j)) (ι i)).app Mg).symm ≪≫
            (Scheme.Modules.pullback (Limits.pullback.fst (ι i) (ι j))).mapIso (ψ i) ≪≫ φ i j =
          (Scheme.Modules.pullbackCongr
              (Limits.pullback.condition : Limits.pullback.fst (ι i) (ι j) ≫ ι i = Limits.pullback.snd (ι i) (ι j) ≫ ι j)).app Mg ≪≫
            ((Scheme.Modules.pullbackComp (Limits.pullback.snd (ι i) (ι j)) (ι j)).app Mg).symm ≪≫
            (Scheme.Modules.pullback (Limits.pullback.snd (ι i) (ι j))).mapIso (ψ j) := by
  have hc : Cocycle ι M φ := hcocycle
  let D : (Mdl.{u}).DescentData ι := datum ι M φ hc
  haveI hsurj : ((Mdl.{u}).toDescentData ι).EssSurj :=
    AlgebraicGeometry.Scheme.Modules.toDescentData_essSurj_of_openCover ι
      (fun y => by obtain ⟨i, x, hx⟩ := hι y; exact ⟨i, x, hx⟩)
  let Mg : Y.Modules := ((Mdl.{u}).toDescentData ι).objPreimage D
  let e : ((Mdl.{u}).toDescentData ι).obj Mg ≅ D := ((Mdl.{u}).toDescentData ι).objObjPreimageIso D
  have hhi : ∀ i, e.hom.hom i ≫ e.inv.hom i = 𝟙 _ := fun i => by
    have := Pseudofunctor.DescentData.comp_hom e.hom e.inv i
    rw [e.hom_inv_id, Pseudofunctor.DescentData.id_hom] at this
    exact this.symm
  have hih : ∀ i, e.inv.hom i ≫ e.hom.hom i = 𝟙 _ := fun i => by
    have := Pseudofunctor.DescentData.comp_hom e.inv e.hom i
    rw [e.inv_hom_id, Pseudofunctor.DescentData.id_hom] at this
    exact this.symm
  let ψ : ∀ i, (Scheme.Modules.pullback (ι i)).obj Mg ≅ M i := fun i => ⟨e.hom.hom i, e.inv.hom i, hhi i, hih i⟩
  refine ⟨Mg, ψ, fun i j => Iso.ext ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom]
  have hcomm := e.hom.comm (Limits.pullback.fst (ι i) (ι j) ≫ ι i) (Limits.pullback.fst (ι i) (ι j))
    (Limits.pullback.snd (ι i) (ι j)) rfl Limits.pullback.condition.symm

  have hD : D.hom (Limits.pullback.fst (ι i) (ι j) ≫ ι i) (Limits.pullback.fst (ι i) (ι j)) (Limits.pullback.snd (ι i) (ι j))
      rfl Limits.pullback.condition.symm = (φ i j).hom := homD_fst_snd ι M φ i j _
  rw [hD, ofObj_hom_eq] at hcomm

  change (Scheme.Modules.pullback (Limits.pullback.fst (ι i) (ι j))).map (e.hom.hom i) ≫ (φ i j).hom =
      ((Scheme.Modules.pullbackComp (Limits.pullback.fst (ι i) (ι j)) (ι i)).hom.app Mg ≫
        (Scheme.Modules.pullbackCongr (rfl : Limits.pullback.fst (ι i) (ι j) ≫ ι i = _)).hom.app Mg) ≫
      (Scheme.Modules.pullbackCongr Limits.pullback.condition.symm.symm).hom.app Mg ≫
      (Scheme.Modules.pullbackComp (Limits.pullback.snd (ι i) (ι j)) (ι j)).inv.app Mg ≫
      (Scheme.Modules.pullback (Limits.pullback.snd (ι i) (ι j))).map (e.hom.hom j) at hcomm
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id] at hcomm
  rw [← cancel_epi ((Scheme.Modules.pullbackComp (Limits.pullback.fst (ι i) (ι j)) (ι i)).hom.app Mg),
    Iso.hom_inv_id_app_assoc]
  first | exact hcomm | simpa [Scheme.Modules.pullbackCongr] using hcomm | (simp [Scheme.Modules.pullbackCongr] at hcomm; exact hcomm)

end S_AlgebraicGeometry_Scheme_Modules_exists_forall_pullback_iso_of_cocycle
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_forall_pullback_iso_of_cocycle (solution)
