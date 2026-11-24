-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PIsoGlueTwo
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_PIsoGlueTwo
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:46.674797+00:00
-- url     : https://prove2.me/theorems/c6e5966f-a9a3-4894-a388-f7d95f16fa37
-- title:
--   PIso Glue Two
-- statement:
--   Definitions and structural lemmas for PIso Glue Two, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PIsoGlueTwo.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsIsoGlueTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGlueModulesStar
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_homEquiv_pullbackCompIso_3c20fd696aa0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso_transMap_app_9788faf886f2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso_unit_app_52e1385b04f1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
namespace IsoGlueTwo
lemma isIso_app_sup {T : TopCat.{0}} {F G : TopCat.Presheaf AddCommGrpCat.{0} T} (hF : F.IsSheaf)
    (hG : G.IsSheaf) (η : F ⟶ G) (U V : Opens T) (hU : IsIso (η.app (op U)))
    (hV : IsIso (η.app (op V))) (hUV : IsIso (η.app (op (U ⊓ V)))) :
    IsIso (η.app (op (U ⊔ V))) := by
  have lF := TopCat.Sheaf.isLimitPullbackCone ⟨F, hF⟩ U V
  have lG := TopCat.Sheaf.isLimitPullbackCone ⟨G, hG⟩ U V
  have n : ∀ {W W' : Opens T} (i : W ⟶ W') [IsIso (η.app (op W'))] [IsIso (η.app (op W))],
      inv (η.app (op W')) ≫ F.map i.op = G.map i.op ≫ inv (η.app (op W)) := by
    intro W W' i _ _
    rw [IsIso.inv_comp_eq, ← Category.assoc, ← η.naturality, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have hw : (G.map (homOfLE le_sup_left : U ⟶ U ⊔ V).op ≫ inv (η.app (op U))) ≫
      F.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op =
      (G.map (homOfLE le_sup_right : V ⟶ U ⊔ V).op ≫ inv (η.app (op V))) ≫
      F.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op := by
    rw [Category.assoc, Category.assoc, n, n, ← G.map_comp_assoc, ← G.map_comp_assoc]
    rfl
  have l₁ := PullbackCone.IsLimit.lift_fst lF _ _ hw
  have l₂ := PullbackCone.IsLimit.lift_snd lF _ _ hw
  change PullbackCone.IsLimit.lift lF _ _ hw ≫ F.map (homOfLE le_sup_left : U ⟶ U ⊔ V).op = _ at l₁
  change PullbackCone.IsLimit.lift lF _ _ hw ≫ F.map (homOfLE le_sup_right : V ⟶ U ⊔ V).op = _ at l₂
  have key : ∀ {W : Opens T} (r : W ⟶ U ⊔ V) (_ : IsIso (η.app (op W)))
      (L : G.obj (op (U ⊔ V)) ⟶ F.obj (op (U ⊔ V)))
      (_ : L ≫ F.map r.op = G.map r.op ≫ inv (η.app (op W))),
      (η.app _ ≫ L) ≫ F.map r.op = 𝟙 _ ≫ F.map r.op ∧
        (L ≫ η.app _) ≫ G.map r.op = 𝟙 _ ≫ G.map r.op := by
    intro W r _ L hL
    constructor
    · rw [Category.assoc, hL, ← Category.assoc, ← η.naturality, Category.assoc, IsIso.hom_inv_id,
        Category.comp_id, Category.id_comp]
    · rw [Category.assoc, ← η.naturality, ← Category.assoc, hL, Category.assoc, IsIso.inv_hom_id,
        Category.comp_id, Category.id_comp]
  refine ⟨⟨PullbackCone.IsLimit.lift lF _ _ hw, ?_, ?_⟩⟩
  · apply PullbackCone.IsLimit.hom_ext lF
    · exact (key _ hU _ l₁).1
    · exact (key _ hV _ l₂).1
  · apply PullbackCone.IsLimit.hom_ext lG
    · exact (key _ hU _ l₁).2
    · exact (key _ hV _ l₂).2
open Scheme.Modules GlueModulesStar
section Glue
variable {X Z₁ Z₂ T : Scheme.{0}}
def restrictOverlap (g : T ⟶ Z₁) (f : Z₁ ⟶ X) {k : T ⟶ X} (e : g ≫ f = k) (M : X.Modules) :
    (pushforward f).obj ((Scheme.Modules.pullback f).obj M) ⟶
      (pushforward k).obj ((Scheme.Modules.pullback k).obj M) :=
  transMap g f e (pullbackCompIso e (Iso.refl _)).inv
lemma unit_restrictOverlap (g : T ⟶ Z₁) (f : Z₁ ⟶ X) {k : T ⟶ X} (e : g ≫ f = k) (M : X.Modules) :
    (pullbackPushforwardAdjunction f).unit.app M ≫ restrictOverlap g f e M =
      (pullbackPushforwardAdjunction k).unit.app M := by
  have h := homEquiv_pullbackCompIso e (Iso.refl ((Scheme.Modules.pullback f).obj M))
    (pullbackCompIso e (Iso.refl _)).inv
  rw [Iso.hom_inv_id, Iso.refl_hom, Adjunction.homEquiv_id, Adjunction.homEquiv_id] at h
  exact h.symm
variable (f₁ : Z₁ ⟶ X) (f₂ : Z₂ ⟶ X) [IsOpenImmersion f₁] [IsOpenImmersion f₂]
  (g₁ : T ⟶ Z₁) (g₂ : T ⟶ Z₂) [IsOpenImmersion g₁] [IsOpenImmersion g₂] {k : T ⟶ X}
  (e₁ : g₁ ≫ f₁ = k) (e₂ : g₂ ≫ f₂ = k)
omit [IsOpenImmersion f₁] [IsOpenImmersion f₂] [IsOpenImmersion g₁] [IsOpenImmersion g₂] in

lemma unit_condition (M : X.Modules) :
    (pullbackPushforwardAdjunction f₁).unit.app M ≫ restrictOverlap g₁ f₁ e₁ M =
      (pullbackPushforwardAdjunction f₂).unit.app M ≫ restrictOverlap g₂ f₂ e₂ M := by
  rw [unit_restrictOverlap, unit_restrictOverlap]
def isLimit (hcov : ⊤ ≤ f₁.opensRange ⊔ f₂.opensRange)
    (h₁₂ : ∀ O : X.Opens, O ≤ f₁.opensRange → f₂ ⁻¹ᵁ O ≤ g₂.opensRange)
    (h₂₁ : ∀ O : X.Opens, O ≤ f₂.opensRange → f₁ ⁻¹ᵁ O ≤ g₁.opensRange) (M : X.Modules) :
    IsLimit (PullbackCone.mk _ _ (unit_condition f₁ f₂ g₁ g₂ e₁ e₂ M)) := by
  set τ₁ := restrictOverlap g₁ f₁ e₁ M
  set τ₂ := restrictOverlap g₂ f₂ e₂ M
  have w := unit_condition f₁ f₂ g₁ g₂ e₁ e₂ M
  suffices hc : IsIso (pullback.lift _ _ w) by
    haveI : IsIso ((limit.isLimit (cospan τ₁ τ₂)).lift (PullbackCone.mk _ _ w)) := hc
    exact IsLimit.ofPointIso (limit.isLimit _)
  have loc : ∀ (W : X.Opens) (a : Bool),
      (W ≤ (if a then f₁.opensRange else f₂.opensRange)) →
      IsIso ((pullback.lift _ _ w).app W) := by
    intro W a hW
    let Fw : X.Modules ⥤ AddCommGrpCat.{0} :=
      toPresheaf X ⋙ (evaluation (X.Opens)ᵒᵖ AddCommGrpCat.{0}).obj (op W)
    have : PreservesLimitsOfShape WalkingCospan
        ((evaluation (X.Opens)ᵒᵖ AddCommGrpCat.{0}).obj (op W)) :=
      evaluation_preservesLimitsOfShape _
    have : PreservesLimitsOfShape WalkingCospan Fw := comp_preservesLimitsOfShape _ _
    cases a
    · simp only [Bool.false_eq_true, ↓reduceIte] at hW
      have : IsIso (Fw.map τ₁) := isIso_transMap_app g₁ f₁ e₁ _ W (h₂₁ W hW)
      have : IsIso (Fw.map (pullback.snd τ₁ τ₂)) := by
        rw [← PreservesPullback.iso_hom_snd Fw]; infer_instance
      have : IsIso (Fw.map ((pullbackPushforwardAdjunction f₂).unit.app M)) :=
        isIso_unit_app f₂ M W hW
      have hc : Fw.map (pullback.lift _ _ w) ≫ Fw.map (pullback.snd τ₁ τ₂) =
          Fw.map ((pullbackPushforwardAdjunction f₂).unit.app M) := by
        rw [← Fw.map_comp, pullback.lift_snd]
      have : IsIso (Fw.map (pullback.lift _ _ w) ≫ Fw.map (pullback.snd τ₁ τ₂)) := by
        rw [hc]; infer_instance
      exact IsIso.of_isIso_comp_right (Fw.map (pullback.lift _ _ w)) (Fw.map (pullback.snd τ₁ τ₂))
    · simp only [↓reduceIte] at hW
      have : IsIso (Fw.map τ₂) := isIso_transMap_app g₂ f₂ e₂ _ W (h₁₂ W hW)
      have : IsIso (Fw.map (pullback.fst τ₁ τ₂)) := by
        rw [← PreservesPullback.iso_hom_fst Fw]; infer_instance
      have : IsIso (Fw.map ((pullbackPushforwardAdjunction f₁).unit.app M)) :=
        isIso_unit_app f₁ M W hW
      have hc : Fw.map (pullback.lift _ _ w) ≫ Fw.map (pullback.fst τ₁ τ₂) =
          Fw.map ((pullbackPushforwardAdjunction f₁).unit.app M) := by
        rw [← Fw.map_comp, pullback.lift_fst]
      have : IsIso (Fw.map (pullback.lift _ _ w) ≫ Fw.map (pullback.fst τ₁ τ₂)) := by
        rw [hc]; infer_instance
      exact IsIso.of_isIso_comp_right (Fw.map (pullback.lift _ _ w)) (Fw.map (pullback.fst τ₁ τ₂))
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro W
  have hW : W ⊓ f₁.opensRange ⊔ W ⊓ f₂.opensRange = W := by
    rw [← inf_sup_left]; exact inf_eq_left.mpr (le_top.trans hcov)
  rw [← hW]
  exact isIso_app_sup M.isSheaf (pullback τ₁ τ₂).isSheaf (pullback.lift _ _ w).mapPresheaf _ _
    (loc _ true inf_le_right) (loc _ false inf_le_right)
    (loc _ true (inf_le_left.trans inf_le_right))
end Glue
end IsoGlueTwo
end
end GroundTheory.Heights₂.Heights.Model


