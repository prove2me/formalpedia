-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.CechTrivialisation.exists_forall_transition_eq_mul_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/c1efe396-c250-5571-8672-53635147f81e

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_unitAutSection_trans_and_unitAutSection_refl
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackUnitIso_conj_app_top_one_eq_appTop
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_forall_transition_eq_mul_mul

set_option autoImplicit false

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace L4Asm

variable {Y : Scheme.{u}}

theorem opHom_eq {A B : (Y.Opens)ᵒᵖ} (f g : A ⟶ B) : f = g :=
  Quiver.Hom.unop_inj (Subsingleton.elim _ _)

theorem presheaf_map_eq {A B : (Y.Opens)ᵒᵖ} (f g : A ⟶ B) : Y.presheaf.map f = Y.presheaf.map g := by
  rw [opHom_eq f g]

noncomputable def secOf (W : Y.Opens) (r : Γ(Y, W)) :
    (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf).sections :=
  PresheafOfModules.sectionsMk
    (fun V => (W : Scheme.{u}).presheaf.map (homOfLE (le_top (a := V.unop))).op (W.topIso.inv r))
    (fun V V' f => by
      change ((W : Scheme.{u}).presheaf.map f) (((W : Scheme.{u}).presheaf.map _) _) =
        ((W : Scheme.{u}).presheaf.map _) _
      rw [← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl)

theorem secOf_val (W : Y.Opens) (r : Γ(Y, W)) (V : ((W : Scheme.{u}).Opens)ᵒᵖ) :
    (secOf W r).val V = (W : Scheme.{u}).presheaf.map (homOfLE (le_top (a := V.unop))).op (W.topIso.inv r) := rfl

noncomputable def mulHom (W : Y.Opens) (r : Γ(Y, W)) :
    SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf ⟶ SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf :=
  (SheafOfModules.unit ((W : Scheme.{u}).ringCatSheaf)).unitHomEquiv.symm (secOf W r)

theorem mulHom_app (W : Y.Opens) (r : Γ(Y, W)) (V : ((W : Scheme.{u}).Opens)ᵒᵖ)
    (x : (W : Scheme.{u}).presheaf.obj V) :
    ((mulHom W r).val.app V).hom x =
      x * (W : Scheme.{u}).presheaf.map (homOfLE (le_top (a := V.unop))).op (W.topIso.inv r) := rfl

theorem secOf_val_mul (W : Y.Opens) (r r' : Γ(Y, W)) (V : ((W : Scheme.{u}).Opens)ᵒᵖ) :
    (W : Scheme.{u}).presheaf.map (homOfLE (le_top (a := V.unop))).op (W.topIso.inv r) *
      (W : Scheme.{u}).presheaf.map (homOfLE (le_top (a := V.unop))).op (W.topIso.inv r') =
    (W : Scheme.{u}).presheaf.map (homOfLE (le_top (a := V.unop))).op (W.topIso.inv (r * r')) := by
  rw [← map_mul, ← map_mul]

theorem mulHom_comp (W : Y.Opens) (r r' : Γ(Y, W)) (h : r * r' = 1) :
    mulHom W r ≫ mulHom W r' = 𝟙 _ := by
  apply (SheafOfModules.unit ((W : Scheme.{u}).ringCatSheaf)).unitHomEquiv.injective
  apply PresheafOfModules.sections_ext
  intro V
  change ((mulHom W r').val.app V).hom (((mulHom W r).val.app V).hom (1 : (W : Scheme.{u}).presheaf.obj V)) =
    (1 : (W : Scheme.{u}).presheaf.obj V)
  rw [mulHom_app, mulHom_app, one_mul, secOf_val_mul, h, map_one, map_one]

noncomputable def mulIso (W : Y.Opens) (r r' : Γ(Y, W)) (h : r * r' = 1) :
    SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf ≅ SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf where
  hom := mulHom W r
  inv := mulHom W r'
  hom_inv_id := mulHom_comp W r r' h
  inv_hom_id := mulHom_comp W r' r (by rw [mul_comm]; exact h)

noncomputable abbrev UMod (W : Y.Opens) : (W : Scheme.{u}).Modules := SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf

noncomputable def mulIsoM (W : Y.Opens) (r r' : Γ(Y, W)) (h : r * r' = 1) : UMod W ≅ UMod W where
  hom := (mulIso W r r' h).hom
  inv := (mulIso W r r' h).inv
  hom_inv_id := (mulIso W r r' h).hom_inv_id
  inv_hom_id := (mulIso W r r' h).inv_hom_id

theorem unitAutSection_mulIso (W : Y.Opens) (r r' : Γ(Y, W)) (h : r * r' = 1) :
    Scheme.Modules.unitAutSection W (mulIsoM W r r' h) = r := by
  unfold Scheme.Modules.unitAutSection
  change W.topIso.hom (((mulHom W r).val.app (op ⊤)).hom (1 : (W : Scheme.{u}).presheaf.obj (op ⊤))) = r
  rw [mulHom_app, one_mul]
  have : (W : Scheme.{u}).presheaf.map (homOfLE (le_top (a := (⊤ : (W : Scheme.{u}).Opens)))).op = 𝟙 _ := by
    rw [← (W : Scheme.{u}).presheaf.map_id]; exact presheaf_map_eq _ _
  rw [this]
  exact W.topIso.inv_hom_id_apply r

theorem map4 {A B C D E : (Y.Opens)ᵒᵖ} (a : A ⟶ B) (b : B ⟶ C) (c' : C ⟶ D) (d : D ⟶ E) (e : A ⟶ E)
    (x : Y.presheaf.obj A) :
    (Y.presheaf.map d).hom ((Y.presheaf.map c').hom ((Y.presheaf.map b).hom ((Y.presheaf.map a).hom x))) =
      (Y.presheaf.map e).hom x := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, presheaf_map_eq _ e]

theorem unitAutSection_conj_mulIso {W W' : Y.Opens} (hle : W' ≤ W) (r r' : Γ(Y, W)) (h : r * r' = 1) :
    Scheme.Modules.unitAutSection W'
      ((Scheme.Modules.pullbackUnitIso (Y.homOfLE hle)).symm ≪≫
        (Scheme.Modules.pullback (Y.homOfLE hle)).mapIso (mulIsoM W r r' h) ≪≫
        Scheme.Modules.pullbackUnitIso (Y.homOfLE hle)) =
      (Y.presheaf.map (homOfLE hle).op).hom r := by
  unfold Scheme.Modules.unitAutSection
  rw [Scheme.Modules.pullbackUnitIso_conj_app_top_one_eq_appTop]
  change W'.topIso.hom ((Y.homOfLE hle).appTop.hom (((mulHom W r).val.app (op ⊤)).hom
    (1 : (W : Scheme.{u}).presheaf.obj (op ⊤)))) = _
  rw [mulHom_app, one_mul, Scheme.homOfLE_appTop, Scheme.Opens.topIso_hom, Scheme.Opens.topIso_inv,
    Scheme.Opens.toScheme_presheaf_map]
  exact map4 _ _ _ _ _ r

end L4Asm

open L4Asm in
theorem solution
    {Y : Scheme.{u}} {𝒱 : Y.OrderedAffineCover} {𝓜 : Y.Modules}
    (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓜)
    (c c' : ∀ a : 𝒱.ι, Γ(Y, 𝒱.U a)) (hc : ∀ a : 𝒱.ι, c a * c' a = 1) :
    ∃ τ' : Scheme.Modules.CechTrivialisation 𝒱 𝓜,
      (∀ a : 𝒱.ι, Scheme.Modules.unitAutSection (𝒱.U a) ((τ a).symm ≪≫ τ' a) = c a) ∧
      ∀ s : 𝒱.Idx 1,
        τ'.transition s = τ.transition s *
          (Y.presheaf.map (homOfLE (𝒱.inter_le s 0)).op).hom (c' (s.1 0)) *
          (Y.presheaf.map (homOfLE (𝒱.inter_le s 1)).op).hom (c (s.1 1)) := by
  classical
  have UM : ∀ (W : Y.Opens) (e e' : UMod W ≅ UMod W), Scheme.Modules.unitAutSection W (e ≪≫ e') =
      Scheme.Modules.unitAutSection W e * Scheme.Modules.unitAutSection W e' :=
    fun W e e' => (Scheme.Modules.unitAutSection_trans_and_unitAutSection_refl W).1 e e'
  have UR : ∀ (W : Y.Opens), Scheme.Modules.unitAutSection W (Iso.refl (UMod W)) = 1 :=
    fun W => (Scheme.Modules.unitAutSection_trans_and_unitAutSection_refl W).2
  let m : ∀ a : 𝒱.ι, UMod (𝒱.U a) ≅ UMod (𝒱.U a) := fun a => mulIsoM (𝒱.U a) (c a) (c' a) (hc a)

  let M : ∀ (a : 𝒱.ι) {W : Y.Opens} (h : W ≤ 𝒱.U a), UMod W ≅ UMod W :=
    fun a W h => (Scheme.Modules.pullbackUnitIso (Y.homOfLE h)).symm ≪≫
      (Scheme.Modules.pullback (Y.homOfLE h)).mapIso (m a) ≪≫ Scheme.Modules.pullbackUnitIso (Y.homOfLE h)
  refine ⟨fun a => τ a ≪≫ m a, fun a => ?_, fun s => ?_⟩
  · exact (congrArg (Scheme.Modules.unitAutSection (𝒱.U a)) (Iso.symm_self_id_assoc (τ a) (m a))).trans
      (unitAutSection_mulIso _ _ _ _)
  · have key : ∀ (a : 𝒱.ι) {W : Y.Opens} (h : W ≤ 𝒱.U a),
        Scheme.Modules.CechTrivialisation.restrict (𝒱 := 𝒱) (𝓜 := 𝓜) (fun a => τ a ≪≫ m a) h =
          τ.restrict h ≪≫ M a h := by
      intro a W h
      apply Iso.ext
      simp only [Scheme.Modules.CechTrivialisation.restrict, M, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
        Functor.mapIso_trans, Category.assoc, Iso.hom_inv_id_assoc]
    have hM : ∀ (a : 𝒱.ι) {W : Y.Opens} (h : W ≤ 𝒱.U a),
        Scheme.Modules.unitAutSection W (M a h) = (Y.presheaf.map (homOfLE h).op).hom (c a) :=
      fun a W h => unitAutSection_conj_mulIso h (c a) (c' a) (hc a)
    have hMs : ∀ (a : 𝒱.ι) {W : Y.Opens} (h : W ≤ 𝒱.U a),
        Scheme.Modules.unitAutSection W (M a h).symm = (Y.presheaf.map (homOfLE h).op).hom (c' a) := by
      intro a W h
      have h1 : Scheme.Modules.unitAutSection W (M a h).symm * Scheme.Modules.unitAutSection W (M a h) = 1 :=
        (UM W (M a h).symm (M a h)).symm.trans
          ((congrArg (Scheme.Modules.unitAutSection W) (Iso.symm_self_id (M a h))).trans (UR W))
      have h2 : (Y.presheaf.map (homOfLE h).op).hom (c a) * (Y.presheaf.map (homOfLE h).op).hom (c' a) = 1 := by
        rw [← map_mul, hc, map_one]
      rw [hM] at h1
      calc Scheme.Modules.unitAutSection W (M a h).symm
          = Scheme.Modules.unitAutSection W (M a h).symm *
              ((Y.presheaf.map (homOfLE h).op).hom (c a) * (Y.presheaf.map (homOfLE h).op).hom (c' a)) := by
            rw [h2, mul_one]
        _ = (Y.presheaf.map (homOfLE h).op).hom (c' a) := by rw [← mul_assoc, h1, one_mul]
    show Scheme.Modules.unitAutSection (𝒱.inter s)
        ((Scheme.Modules.CechTrivialisation.restrict (fun a => τ a ≪≫ m a) (𝒱.inter_le s 0)).symm ≪≫
          Scheme.Modules.CechTrivialisation.restrict (fun a => τ a ≪≫ m a) (𝒱.inter_le s 1)) = _
    rw [key, key]
    show _ = Scheme.Modules.unitAutSection (𝒱.inter s)
        ((τ.restrict (𝒱.inter_le s 0)).symm ≪≫ τ.restrict (𝒱.inter_le s 1)) * _ * _
    have e1 : (τ.restrict (𝒱.inter_le s 0) ≪≫ M (s.1 0) (𝒱.inter_le s 0)).symm ≪≫
          (τ.restrict (𝒱.inter_le s 1) ≪≫ M (s.1 1) (𝒱.inter_le s 1)) =
        (M (s.1 0) (𝒱.inter_le s 0)).symm ≪≫
          (((τ.restrict (𝒱.inter_le s 0)).symm ≪≫ τ.restrict (𝒱.inter_le s 1)) ≪≫ M (s.1 1) (𝒱.inter_le s 1)) := by
      apply Iso.ext; rfl
    calc Scheme.Modules.unitAutSection (𝒱.inter s)
          ((τ.restrict (𝒱.inter_le s 0) ≪≫ M (s.1 0) (𝒱.inter_le s 0)).symm ≪≫
            (τ.restrict (𝒱.inter_le s 1) ≪≫ M (s.1 1) (𝒱.inter_le s 1)))
        = Scheme.Modules.unitAutSection (𝒱.inter s) ((M (s.1 0) (𝒱.inter_le s 0)).symm ≪≫
            (((τ.restrict (𝒱.inter_le s 0)).symm ≪≫ τ.restrict (𝒱.inter_le s 1)) ≪≫ M (s.1 1) (𝒱.inter_le s 1))) :=
          congrArg _ e1
      _ = Scheme.Modules.unitAutSection (𝒱.inter s) (M (s.1 0) (𝒱.inter_le s 0)).symm *
            (Scheme.Modules.unitAutSection (𝒱.inter s)
                ((τ.restrict (𝒱.inter_le s 0)).symm ≪≫ τ.restrict (𝒱.inter_le s 1)) *
              Scheme.Modules.unitAutSection (𝒱.inter s) (M (s.1 1) (𝒱.inter_le s 1))) := by
          refine (UM _ _ _).trans ?_
          exact congrArg _ (UM _ _ _)
      _ = _ := by rw [hMs, hM]; ring

end S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_forall_transition_eq_mul_mul
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_forall_transition_eq_mul_mul (solution)
