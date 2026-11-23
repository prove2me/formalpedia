-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:28:06.045324+00:00
-- url     : https://prove2.me/theorems/b3ad3df6-56da-4c9f-b56a-da145a282875
-- title:
--   Is Iso Normalization Pullback Of To Integral Closure
-- statement:
--   Definitions and structural lemmas for Is Iso Normalization Pullback Of To Integral Closure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
namespace GlobalTheory
theorem hom_ext_of_isSchemeTheoreticallyDominant {W X T Z : Scheme.{u}} (j : W ⟶ X)
    [IsSchemeTheoreticallyDominant j] {m m' : X ⟶ T} (g : T ⟶ Z) [IsSeparated g]
    (h₁ : j ≫ m = j ≫ m') (h₂ : m ≫ g = m' ≫ g) : m = m' := by
  let a : Over.mk (m ≫ g) ⟶ Over.mk g := Over.homMk m
  let b : Over.mk (m ≫ g) ⟶ Over.mk g := Over.homMk m' h₂.symm
  have : IsSeparated (Over.mk g).hom := ‹_›
  let c : Over.mk (j ≫ m ≫ g) ⟶ Over.mk (m ≫ g) := Over.homMk j
  have hc : c ≫ a = c ≫ b := by ext1; exact h₁
  have hk : (equalizer.ι a b).left.ker = ⊥ := by
    have e : (equalizer.lift c hc).left ≫ (equalizer.ι a b).left = j := by
      rw [← Over.comp_left, equalizer.lift_ι]; rfl
    have := (equalizer.lift c hc).left.le_ker_comp (equalizer.ι a b).left
    rw [e] at this
    exact le_bot_iff.mp (this.trans j.ker_eq_bot.le)
  have : IsIso (equalizer.ι a b).left := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hk
  rw [← cancel_epi (equalizer.ι a b).left]
  exact congr($(equalizer.condition a b).left)
theorem isSchemeTheoreticallyDominant_of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSchemeTheoreticallyDominant (f ≫ g)] : IsSchemeTheoreticallyDominant g :=
  ⟨le_bot_iff.mp ((f.le_ker_comp g).trans (f ≫ g).ker_eq_bot.le)⟩
instance isSchemeTheoreticallyDominant_toNormalization {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] : IsSchemeTheoreticallyDominant f.toNormalization :=
  ⟨f.ker_toNormalization⟩
section Lift
variable {X Y T Z : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
theorem normalization_hom_ext {m m' : f.normalization ⟶ T} (g : T ⟶ Z) [IsSeparated g]
    (h₁ : f.toNormalization ≫ m = f.toNormalization ≫ m') (h₂ : m ≫ g = m' ≫ g) : m = m' :=
  hom_ext_of_isSchemeTheoreticallyDominant f.toNormalization g h₁ h₂
noncomputable def normalizationLift (a : X ⟶ T) (g : T ⟶ Z) [IsIntegralHom g] (b : Y ⟶ Z)
    (H : a ≫ g = f ≫ b) : f.normalization ⟶ T :=
  f.normalizationDesc (pullback.lift a f H) (pullback.snd g b) (pullback.lift_snd ..).symm ≫
    pullback.fst g b
variable (a : X ⟶ T) (g : T ⟶ Z) [IsIntegralHom g] (b : Y ⟶ Z) (H : a ≫ g = f ≫ b)
@[reassoc (attr := simp)]
theorem toNormalization_normalizationLift :
    f.toNormalization ≫ normalizationLift f a g b H = a := by
  simp [normalizationLift, pullback.lift_fst]
@[reassoc (attr := simp)]
theorem normalizationLift_comp :
    normalizationLift f a g b H ≫ g = f.fromNormalization ≫ b := by
  simp [normalizationLift, pullback.condition]
theorem eq_normalizationLift {m : f.normalization ⟶ T} (h₁ : f.toNormalization ≫ m = a)
    (h₂ : m ≫ g = f.fromNormalization ≫ b) : m = normalizationLift f a g b H :=
  normalization_hom_ext f g (by simp [h₁]) (by simp [h₂])
instance isIntegralHom_normalizationLift [IsIntegralHom b] :
    IsIntegralHom (normalizationLift f a g b H) :=
  have : IsIntegralHom (normalizationLift f a g b H ≫ g) := by
    rw [normalizationLift_comp]; infer_instance
  .of_comp _ g
end Lift
section Map
variable {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Scheme.{u}} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃)
  [QuasiCompact f₁] [QuasiSeparated f₁] [QuasiCompact f₂] [QuasiSeparated f₂]
  [QuasiCompact f₃] [QuasiSeparated f₃]
noncomputable def normalizationMap (a : X₁ ⟶ X₂) (b : Y₁ ⟶ Y₂) (H : a ≫ f₂ = f₁ ≫ b) :
    f₁.normalization ⟶ f₂.normalization :=
  normalizationLift f₁ (a ≫ f₂.toNormalization) f₂.fromNormalization b (by simp [H])
variable (a : X₁ ⟶ X₂) (b : Y₁ ⟶ Y₂) (H : a ≫ f₂ = f₁ ≫ b)
@[reassoc (attr := simp)]
theorem toNormalization_normalizationMap :
    f₁.toNormalization ≫ normalizationMap f₁ f₂ a b H = a ≫ f₂.toNormalization := by
  simp [normalizationMap]
@[reassoc (attr := simp)]
theorem normalizationMap_fromNormalization :
    normalizationMap f₁ f₂ a b H ≫ f₂.fromNormalization = f₁.fromNormalization ≫ b := by
  simp [normalizationMap]
theorem eq_normalizationMap {m : f₁.normalization ⟶ f₂.normalization}
    (h₁ : f₁.toNormalization ≫ m = a ≫ f₂.toNormalization)
    (h₂ : m ≫ f₂.fromNormalization = f₁.fromNormalization ≫ b) :
    m = normalizationMap f₁ f₂ a b H :=
  eq_normalizationLift f₁ _ _ _ _ h₁ h₂
@[simp]
theorem normalizationMap_id :
    normalizationMap f₁ f₁ (𝟙 _) (𝟙 _) (by simp) = 𝟙 _ :=
  (eq_normalizationMap f₁ f₁ _ _ _ (by simp) (by simp)).symm
@[reassoc]
theorem normalizationMap_comp (a' : X₂ ⟶ X₃) (b' : Y₂ ⟶ Y₃) (H' : a' ≫ f₃ = f₂ ≫ b') :
    normalizationMap f₁ f₂ a b H ≫ normalizationMap f₂ f₃ a' b' H' =
      normalizationMap f₁ f₃ (a ≫ a') (b ≫ b') (by simp [H', reassoc_of% H]) :=
  eq_normalizationMap f₁ f₃ _ _ _ (by simp) (by simp)
instance isIntegralHom_normalizationMap [IsIntegralHom b] :
    IsIntegralHom (normalizationMap f₁ f₂ a b H) :=
  isIntegralHom_normalizationLift ..
instance isSchemeTheoreticallyDominant_normalizationMap [IsSchemeTheoreticallyDominant a] :
    IsSchemeTheoreticallyDominant (normalizationMap f₁ f₂ a b H) :=
  have : IsSchemeTheoreticallyDominant (f₁.toNormalization ≫ normalizationMap f₁ f₂ a b H) := by
    rw [toNormalization_normalizationMap]; infer_instance
  isSchemeTheoreticallyDominant_of_comp f₁.toNormalization _
instance isIso_normalizationMap [IsIso a] [IsIntegralHom b] :
    IsIso (normalizationMap f₁ f₂ a b H) := by
  refine ⟨normalizationLift f₂ (inv a ≫ f₁.toNormalization) (f₁.fromNormalization ≫ b) (𝟙 _)
    (by simp [← H]), ?_, ?_⟩
  · exact normalization_hom_ext f₁ (f₁.fromNormalization ≫ b) (by simp) (by simp)
  · refine normalization_hom_ext f₂ f₂.fromNormalization (by simp) ?_
    simp
noncomputable def normalizationMapIso (a : X₁ ≅ X₂) (b : Y₁ ≅ Y₂)
    (H : a.hom ≫ f₂ = f₁ ≫ b.hom) : f₁.normalization ≅ f₂.normalization :=
  asIso (normalizationMap f₁ f₂ a.hom b.hom H)
@[simp]
theorem normalizationMapIso_hom (a : X₁ ≅ X₂) (b : Y₁ ≅ Y₂) (H : a.hom ≫ f₂ = f₁ ≫ b.hom) :
    (normalizationMapIso f₁ f₂ a b H).hom = normalizationMap f₁ f₂ a.hom b.hom H := rfl
end Map
section Trans
variable {X T Y : Scheme.{u}} (f₁ : X ⟶ T) (f₂ : T ⟶ Y) [IsIntegralHom f₂]
  [QuasiCompact f₁] [QuasiSeparated f₁] (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
  (H : f = f₁ ≫ f₂)
noncomputable def normalizationTransIso : f₁.normalization ≅ f.normalization :=
  asIso (normalizationMap f₁ f (𝟙 X) f₂ (by simp [H]))
@[reassoc (attr := simp)]
theorem toNormalization_normalizationTransIso_hom :
    f₁.toNormalization ≫ (normalizationTransIso f₁ f₂ f H).hom = f.toNormalization := by
  simp [normalizationTransIso]
@[reassoc (attr := simp)]
theorem normalizationTransIso_hom_fromNormalization :
    (normalizationTransIso f₁ f₂ f H).hom ≫ f.fromNormalization = f₁.fromNormalization ≫ f₂ := by
  simp [normalizationTransIso]
@[reassoc (attr := simp)]
theorem toNormalization_normalizationTransIso_inv :
    f.toNormalization ≫ (normalizationTransIso f₁ f₂ f H).inv = f₁.toNormalization := by
  simp [Iso.comp_inv_eq]
@[reassoc (attr := simp)]
theorem normalizationTransIso_inv_fromNormalization :
    (normalizationTransIso f₁ f₂ f H).inv ≫ f₁.fromNormalization =
      f.normalizationDesc f₁ f₂ H :=
  normalization_hom_ext f f₂ (by simp) (by simp [Iso.inv_comp_eq])
theorem isIso_normalizationDesc_iff :
    IsIso (f.normalizationDesc f₁ f₂ H) ↔ IsIso f₁.fromNormalization := by
  rw [← normalizationTransIso_inv_fromNormalization, isIso_comp_left_iff]
end Trans
instance isIso_toNormalization_fromNormalization {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    [QuasiSeparated f] : IsIso f.toNormalization.fromNormalization := by
  rw [← isIso_normalizationDesc_iff f.toNormalization f.fromNormalization f (by simp)]
  have : f.normalizationDesc f.toNormalization f.fromNormalization (by simp) = 𝟙 _ :=
    normalization_hom_ext f f.fromNormalization (by simp) (by simp)
  rw [this]
  infer_instance
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open TensorProduct in

theorem isIso_normalizationPullback_of_toIntegralClosure {X S Y : Scheme.{u}} (f : X ⟶ S)
    (g : Y ⟶ S) [QuasiCompact f] [QuasiSeparated f] [Flat g]
    (hg : ∀ y : Y, ∃ (U : S.Opens) (_ : IsAffineOpen U) (V : Y.Opens) (_ : IsAffineOpen V)
      (hVU : V ≤ g ⁻¹ᵁ U), y ∈ V ∧ ∀ (B : Type u) [CommRing B] [Algebra Γ(S, U) B],
        letI := (g.appLE U V hVU).hom.toAlgebra
        Function.Bijective (TensorProduct.toIntegralClosure Γ(S, U) Γ(Y, V) B)) :
    IsIso (f.normalizationPullback g) := by
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := .isomorphisms _) fun x ↦ ?_
  obtain ⟨U, hU, V, hV, hVU, hxV, hB⟩ := hg (pullback.snd f.fromNormalization g x)
  let W := pullback.snd (Scheme.Hom.fromNormalization f) g ⁻¹ᵁ V
  refine ⟨W, hxV, (isIso_morphismRestrict_iff_isIso_app _ (U := W) (hV.preimage _)).mpr ?_⟩
  have := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (.of_hasPullback f.fromNormalization g) hVU le_rfl (UY := W)
    (by simp_rw [W, ← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage,
      ← Scheme.Hom.preimage_inf, inf_eq_right.mpr hVU]) hU hV
    (hU.preimage f.fromNormalization).isCompact (hU.preimage f.fromNormalization).isQuasiSeparated
  rw [← @isIso_comp_left_iff _ _ _ _ _ _ _ this,
    ← isIso_comp_left_iff (pushout.congrHom f.fromNormalization.app_eq_appLE rfl).hom]
  algebraize [(f.app U).hom, (g.appLE U V hVU).hom, ((pullback.snd f g).app V).hom]
  have := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (.of_hasPullback f g) hVU le_rfl (UY := pullback.snd f g ⁻¹ᵁ V)
    (by simp_rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage,
      ← Scheme.Hom.preimage_inf, inf_eq_right.mpr hVU]) hU hV (f.isCompact_preimage hU.isCompact)
    (f.isQuasiSeparated_preimage hU.isQuasiSeparated)
  let e₀ := (CommRingCat.isPushout_tensorProduct ..).flip.isoPushout ≪≫
    (pushout.congrHom f.app_eq_appLE rfl ≪≫ @asIso _ _ _ _ _ this :)
  let e : Γ(Y, V) ⊗[Γ(S, U)] Γ(X, f ⁻¹ᵁ U) ≃ₐ[Γ(Y, V)] Γ(pullback f g, pullback.snd f g ⁻¹ᵁ V) :=
    { toRingEquiv := e₀.commRingCatIsoToRingEquiv,
      commutes' r := by
        change (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ e₀.hom) r =
          (pullback.snd f g).app V r
        congr 2
        simp [e₀, pushout.inr_desc_assoc, Scheme.Hom.app_eq_appLE] }
  let ψ : Γ(Y, V) ⊗[Γ(S, U)] integralClosure Γ(S, U) Γ(X, f ⁻¹ᵁ U) →ₐ[Γ(Y, V)]
      integralClosure Γ(Y, V) Γ(pullback f g, pullback.snd f g ⁻¹ᵁ V) :=
    e.mapIntegralClosure.toAlgHom.comp (TensorProduct.toIntegralClosure _ _ _)
  have hψ : Function.Bijective ψ := e.mapIntegralClosure.bijective.comp
    (hB _)
  let φ : pushout (f.fromNormalization.app U) (g.appLE U V hVU) ⟶
      Γ((pullback.snd f g).normalization, f.normalizationPullback g ⁻¹ᵁ W) :=
    pushout.map _ _ (CommRingCat.ofHom (algebraMap Γ(S, U) (integralClosure Γ(S, U) Γ(X, f ⁻¹ᵁ U))))
      (g.appLE U V hVU) (f.normalizationObjIso hU).hom (𝟙 _) (𝟙 _)
      (by simp [Scheme.Hom.fromNormalization_app _ hU]) (by simp) ≫
    (CommRingCat.isPushout_tensorProduct ..).flip.isoPushout.inv ≫
    (RingEquiv.ofBijective ψ.toRingHom hψ).toCommRingCatIso.hom ≫
    ((pullback.snd f g).normalizationObjIso hV).inv ≫
    (pullback.snd f g).normalization.presheaf.map (eqToHom
      (by simp only [W, ← Scheme.Hom.comp_preimage, Scheme.Hom.normalizationPullback_snd])).op
  convert! show IsIso φ by dsimp only [φ]; infer_instance using 1
  ext1
  · dsimp [φ]
    simp only [Scheme.Hom.app_eq_appLE, colimit.ι_desc_assoc, span_left, PushoutCocone.mk_pt,
      PushoutCocone.mk_ι_app, Category.id_comp, Scheme.Hom.appLE_comp_appLE, eqToHom_op,
      Category.assoc, IsPushout.inl_isoPushout_inv_assoc]
    simp_rw [← Category.assoc, ← IsIso.comp_inv_eq]
    simp only [← Functor.map_inv, inv_eqToHom, Scheme.Hom.appLE_map, IsIso.Iso.inv_inv,
      Category.assoc]
    have : Mono (CommRingCat.ofHom (integralClosure Γ(Y, V)
        Γ(pullback f g, pullback.snd f g ⁻¹ᵁ V)).val.toRingHom) :=
      ConcreteCategory.mono_of_injective _ Subtype.val_injective
    rw [← cancel_mono (CommRingCat.ofHom (Subalgebra.val _).toRingHom)]
    simp only [Category.assoc, Scheme.Hom.normalizationObjIso_hom_val, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.toNormalization_normalizationPullback_fst, ← CommRingCat.ofHom_comp]
    have H : pullback.snd f g ⁻¹ᵁ V ≤ pullback.fst f g ⁻¹ᵁ f ⁻¹ᵁ U := by
      rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage]
      exact Scheme.Hom.preimage_mono _ hVU
    trans (f.normalizationObjIso hU).hom ≫ CommRingCat.ofHom
        (integralClosure Γ(S, U) Γ(X, f ⁻¹ᵁ U)).val.toRingHom ≫ (pullback.fst f g).appLE _ _ H
    · rw [reassoc_of% Scheme.Hom.normalizationObjIso_hom_val, Scheme.Hom.appLE_comp_appLE]
    · congr 1
      ext x
      change (pullback.fst f g).appLE _ _ H x = _
      trans (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom ≫ e₀.hom) x
      · congr 2; simp [e₀, pushout.inl_desc_assoc]
      · simp [ψ, toIntegralClosure, e]; rfl
  · dsimp [φ]
    simp only [Scheme.Hom.app_eq_appLE, colimit.ι_desc_assoc, span_right, PushoutCocone.mk_pt,
      PushoutCocone.mk_ι_app, Category.id_comp, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.normalizationPullback_snd, eqToHom_op, IsPushout.inr_isoPushout_inv_assoc]
    simp_rw [← Category.assoc, ← IsIso.comp_inv_eq]
    simp only [← Functor.map_inv, inv_eqToHom, Scheme.Hom.appLE_map, ← Scheme.Hom.app_eq_appLE,
      Scheme.Hom.fromNormalization_app _ hV, IsIso.Iso.inv_inv, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    exact congr(CommRingCat.ofHom $(ψ.comp_algebraMap.symm))
class PreservesNormalization {Y S : Scheme.{u}} (g : Y ⟶ S) : Prop where

  isIso_normalizationPullback : ∀ {X : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f],
    IsIso (f.normalizationPullback g)
attribute [instance] PreservesNormalization.isIso_normalizationPullback
instance (priority := 900) PreservesNormalization.of_smooth {Y S : Scheme.{u}} (g : Y ⟶ S)
    [Smooth g] : PreservesNormalization g :=
  ⟨fun _ _ _ ↦ inferInstance⟩
theorem PreservesNormalization.of_isLocalization {Y S : Scheme.{u}} (g : Y ⟶ S)
    (hg : ∀ y : Y, ∃ (U : S.Opens) (_ : IsAffineOpen U) (V : Y.Opens) (_ : IsAffineOpen V)
      (hVU : V ≤ g ⁻¹ᵁ U) (M : Submonoid Γ(S, U)), y ∈ V ∧
        letI := (g.appLE U V hVU).hom.toAlgebra
        IsLocalization M Γ(Y, V)) : PreservesNormalization g := by
  have : Flat g := by
    refine HasRingHomProperty.iff_exists_appLE (P := @Flat)
      (RingHom.Flat.stableUnderComposition.stableUnderCompositionWithLocalizationAway
        RingHom.Flat.holdsForLocalizationAway).left |>.mpr
      fun y ↦ ?_
    obtain ⟨U, hU, V, hV, hVU, M, hy, h⟩ := hg y
    let := (g.appLE U V hVU).hom.toAlgebra
    exact ⟨⟨U, hU⟩, ⟨V, hV⟩, hy, hVU, IsLocalization.flat _ M⟩
  refine ⟨fun f _ _ ↦ isIso_normalizationPullback_of_toIntegralClosure f g fun y ↦ ?_⟩
  obtain ⟨U, hU, V, hV, hVU, M, hy, h⟩ := hg y
  let := (g.appLE U V hVU).hom.toAlgebra
  exact ⟨U, hU, V, hV, hVU, hy, fun B _ _ ↦
    TensorProduct.toIntegralClosure_bijective_of_isLocalization M⟩
theorem PreservesNormalization.of_isPullback_localization {R R' : Type u} [CommRing R]
    [CommRing R'] [Algebra R R'] (M : Submonoid R) [IsLocalization M R'] {Y S : Scheme.{u}}
    {g : Y ⟶ S} {t : Y ⟶ Spec (.of R')} {s : S ⟶ Spec (.of R)}
    (h : IsPullback g t s (Spec.map (CommRingCat.ofHom (algebraMap R R')))) :
    PreservesNormalization g := by
  have : IsAffineHom g := MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
  refine .of_isLocalization g fun y ↦ ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (g y)) isOpen_univ
  have hp := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := U) (UY := g ⁻¹ᵁ U)
    le_top le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen h _ _ _
      (isAffineOpen_top _) (isAffineOpen_top _) hU)
  have hp' : IsPushout ((Scheme.ΓSpecIso (.of R)).inv ≫ s.appLE ⊤ U le_top)
      (CommRingCat.ofHom (algebraMap R R')) (g.appLE U (g ⁻¹ᵁ U) le_rfl)
      ((Scheme.ΓSpecIso (.of R')).inv ≫ t.appLE ⊤ (g ⁻¹ᵁ U) le_top) := by
    refine hp.of_iso (Scheme.ΓSpecIso _) (.refl _) (Scheme.ΓSpecIso _) (.refl _) (by simp) ?_
      (by simp) (by simp)
    exact Scheme.ΓSpecIso_naturality _
  algebraize [((Scheme.ΓSpecIso (.of R)).inv ≫ s.appLE ⊤ U le_top).hom,
    (g.appLE U (g ⁻¹ᵁ U) le_rfl).hom,
    ((Scheme.ΓSpecIso (.of R')).inv ≫ t.appLE ⊤ (g ⁻¹ᵁ U) le_top).hom,
    (((Scheme.ΓSpecIso (.of R)).inv ≫ s.appLE ⊤ U le_top) ≫ g.appLE U (g ⁻¹ᵁ U) le_rfl).hom]
  have : IsScalarTower R Γ(S, U) Γ(Y, g ⁻¹ᵁ U) := .of_algebraMap_eq' rfl
  have : IsScalarTower R R' Γ(Y, g ⁻¹ᵁ U) := .of_algebraMap_eq' congr($(hp'.w).hom)
  have : Algebra.IsPushout R Γ(S, U) R' Γ(Y, g ⁻¹ᵁ U) :=
    CommRingCat.isPushout_iff_isPushout.mp hp'
  exact ⟨U, hU, g ⁻¹ᵁ U, hU.preimage g, le_rfl, Algebra.algebraMapSubmonoid Γ(S, U) M, hxU,
    (Algebra.isLocalization_iff_isPushout M R').mpr this⟩
section BaseChange
variable {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {a : X' ⟶ X} {b : Y' ⟶ Y}
  [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
@[reassoc]
theorem normalizationPullback_fst (f : X ⟶ Y) (b : Y' ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    f.normalizationPullback b ≫ pullback.fst _ _ =
      normalizationMap (pullback.snd f b) f (pullback.fst f b) b pullback.condition :=
  eq_normalizationMap _ _ _ _ _ (by simp) (by simp [pullback.condition])
theorem isPullback_normalizationMap (h : IsPullback a f' f b) [PreservesNormalization b] :
    IsPullback (normalizationMap f' f a b h.w) f'.fromNormalization f.fromNormalization b := by
  let e := normalizationMap f' (pullback.snd f b) h.isoPullback.hom (𝟙 _) (by simp)
  refine IsPullback.of_iso_pullback ⟨by simp⟩ (asIso (e ≫ f.normalizationPullback b)) ?_ ?_
  · simp [e, normalizationPullback_fst, normalizationMap_comp]
  · simp [e]
theorem PreservesNormalization.of_isPullback (b : Y' ⟶ Y)
    (hb : ∀ {X : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f],
      IsPullback (normalizationMap (pullback.snd f b) f (pullback.fst f b) b pullback.condition)
        (pullback.snd f b).fromNormalization f.fromNormalization b) :
    PreservesNormalization b := by
  refine ⟨fun f _ _ ↦ ?_⟩
  have : f.normalizationPullback b = (hb f).isoPullback.hom := by
    apply pullback.hom_ext <;> simp [normalizationPullback_fst]
  rw [this]
  infer_instance
instance PreservesNormalization.comp {Y'' : Scheme.{u}} (b' : Y'' ⟶ Y') (b : Y' ⟶ Y)
    [PreservesNormalization b'] [PreservesNormalization b] : PreservesNormalization (b' ≫ b) := by
  refine .of_isPullback _ fun f _ _ ↦ ?_
  let c : pullback f (b' ≫ b) ⟶ pullback f b :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ b') (by simp [pullback.condition])
  have hc : c ≫ pullback.fst f b = pullback.fst _ _ := pullback.lift_fst ..
  have h : IsPullback c (pullback.snd f (b' ≫ b)) (pullback.snd f b) b' :=
    IsPullback.of_right (by rw [hc]; exact .of_hasPullback _ _) (pullback.lift_snd ..)
      (.of_hasPullback f b)
  have := (isPullback_normalizationMap h).paste_horiz
    (isPullback_normalizationMap (.of_hasPullback f b))
  rw [normalizationMap_comp] at this
  simpa only [hc] using this
end BaseChange
section Mono
variable {X Y V : Scheme.{u}} (f' : X ⟶ V) (b : V ⟶ Y) [Mono b] (f : X ⟶ Y) (H : f = f' ≫ b)
variable [QuasiCompact f] [QuasiSeparated f] [PreservesNormalization b]
end Mono
section Localization
variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] (M : Submonoid R)
  [IsLocalization M R'] {Y Y' : Scheme.{u}} {b : Y' ⟶ Y} {t : Y' ⟶ Spec (.of R')}
  {s : Y ⟶ Spec (.of R)}
end Localization
example : PreservesNormalization (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) :=
  .of_isPullback_localization (nonZeroDivisors ℤ) (IsPullback.of_id_snd)
example {Y S : Scheme.{u}} (g : Y ⟶ S) [Etale g] : PreservesNormalization g := inferInstance
section Flat
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
  {R : Type u} [CommRing R]
end Flat
section Sections
theorem app_presheaf_map_apply {X Y : Scheme.{u}} (q : X ⟶ Y) {V W : Y.Opens} (h : V ≤ W)
    (t : Γ(Y, W)) : q.app V (Y.presheaf.map (homOfLE h).op t) =
      X.presheaf.map (homOfLE (q.preimage_mono h)).op (q.app W t) :=
  congr($(q.naturality (homOfLE h).op) t)
theorem presheaf_map_map_apply {X : Scheme.{u}} {U V W : X.Opens} (h : U ≤ V) (h' : V ≤ W)
    (t : Γ(X, W)) : X.presheaf.map (homOfLE h).op (X.presheaf.map (homOfLE h').op t) =
      X.presheaf.map (homOfLE (h.trans h')).op t := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl
theorem mem_range_app_of_locally {X Y : Scheme.{u}} (q : X ⟶ Y) [QuasiCompact q]
    [IsSchemeTheoreticallyDominant q] (W : Y.Opens) (s : Γ(X, q ⁻¹ᵁ W))
    (h : ∀ y ∈ W, ∃ (V : Y.Opens) (hV : V ≤ W), y ∈ V ∧
      X.presheaf.map (homOfLE (q.preimage_mono hV)).op s ∈ Set.range (q.app V)) :
    s ∈ Set.range (q.app W) := by
  choose V hV hyV t ht using fun y : W ↦ h y.1 y.2
  obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' V W (fun y ↦ homOfLE (hV y))
    (fun y hy ↦ Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hyV _⟩) t (fun y y' ↦ by
      apply q.app_injective (V y ⊓ V y')
      refine (app_presheaf_map_apply q inf_le_left _).trans
        (.trans ?_ (app_presheaf_map_apply q inf_le_right _).symm)
      rw [ht, ht, presheaf_map_map_apply, presheaf_map_map_apply])
  refine ⟨a, X.sheaf.eq_of_locally_eq' (fun y ↦ q ⁻¹ᵁ V y) (q ⁻¹ᵁ W)
    (fun y ↦ homOfLE (q.preimage_mono (hV y)))
    (fun x hx ↦ Opens.mem_iSup.mpr ⟨⟨q x, hx⟩, hyV _⟩) _ _ fun y ↦ ?_⟩
  refine (app_presheaf_map_apply q (hV y) a).symm.trans (.trans ?_ (ht y))
  exact congrArg _ (ha y)
theorem mem_range_app_of_forall_isAffineOpen {X Y : Scheme.{u}} (q : X ⟶ Y) [QuasiCompact q]
    [IsSchemeTheoreticallyDominant q] (W : Y.Opens) (s : Γ(X, q ⁻¹ᵁ W))
    (h : ∀ (V : Y.Opens) (_ : IsAffineOpen V) (hV : V ≤ W),
      X.presheaf.map (homOfLE (q.preimage_mono hV)).op s ∈ Set.range (q.app V)) :
    s ∈ Set.range (q.app W) :=
  mem_range_app_of_locally q W s fun y hy ↦ by
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVW⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hy W.isOpen
    exact ⟨V, hVW, hyV, h V hV hVW⟩
theorem isIso_fromNormalization_iff {X T : Scheme.{u}} (j : X ⟶ T) [QuasiCompact j]
    [QuasiSeparated j] : IsIso j.fromNormalization ↔ ∀ W : T.Opens, IsAffineOpen W →
      Function.Injective (j.app W) ∧
        ∀ t : Γ(X, j ⁻¹ᵁ W), (j.app W).hom.IsIntegralElem t → t ∈ Set.range (j.app W) := by
  have key (W : T.Opens) (hW : IsAffineOpen W) : IsIso (j.fromNormalization.app W) ↔
      Function.Injective (j.app W) ∧
        ∀ t : Γ(X, j ⁻¹ᵁ W), (j.app W).hom.IsIntegralElem t → t ∈ Set.range (j.app W) := by
    let := (j.app W).hom.toAlgebra
    rw [j.fromNormalization_app hW, isIso_comp_right_iff, ConcreteCategory.isIso_iff_bijective]
    refine and_congr ⟨fun h ↦ Subtype.val_injective.comp h, fun h ↦ .of_comp (f := Subtype.val) h⟩
      ⟨fun h t ht ↦ ?_, fun h t ↦ ?_⟩
    · obtain ⟨a, ha⟩ := h ⟨t, ht⟩
      exact ⟨a, congrArg Subtype.val ha⟩
    · obtain ⟨a, ha⟩ := h t.1 t.2
      exact ⟨a, Subtype.ext ha⟩
  refine ⟨fun _ W hW ↦ (key W hW).mp inferInstance, fun h ↦ ?_⟩
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := .isomorphisms _) _
    (iSup_affineOpens_eq_top T)).mpr fun W ↦ ?_
  exact (isIso_morphismRestrict_iff_isIso_app _ W.2).mpr ((key W W.2).mpr (h W W.2))
theorem mem_range_toNormalization_app {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    [QuasiSeparated f] (W : f.normalization.Opens) (t : Γ(X, f.toNormalization ⁻¹ᵁ W))
    (ht : (f.toNormalization.app W).hom.IsIntegralElem t) :
    t ∈ Set.range (f.toNormalization.app W) := by
  refine mem_range_app_of_forall_isAffineOpen _ W t fun V hV hVW ↦ ?_
  refine (((isIso_fromNormalization_iff f.toNormalization).mp inferInstance) V hV).2 _ ?_
  obtain ⟨p, hp, e⟩ := ht
  refine ⟨p.map (f.normalization.presheaf.map (homOfLE hVW).op).hom, hp.map _, ?_⟩
  have := congrArg (X.presheaf.map (homOfLE (f.toNormalization.preimage_mono hVW)).op).hom e
  rw [map_zero, Polynomial.hom_eval₂] at this
  rw [Polynomial.eval₂_map, ← this]
  congr 1
  ext a
  exact app_presheaf_map_apply f.toNormalization hVW a
end Sections
section Action
variable {G : Type v} [Group G] {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
noncomputable def normalizationAction (ρ : G →* Aut X) (σ : G →* Aut Y)
    (H : ∀ g, (ρ g).hom ≫ f = f ≫ (σ g).hom) : G →* Aut f.normalization :=
  MonoidHom.mk' (fun g ↦ normalizationMapIso f f (ρ g) (σ g) (H g)) fun g h ↦ by
    refine Iso.ext (eq_normalizationMap f f _ _ (H (g * h)) ?_ ?_).symm
    · change f.toNormalization ≫ normalizationMap f f _ _ (H h) ≫ normalizationMap f f _ _ (H g) = _
      rw [map_mul]
      change _ = ((ρ h).hom ≫ (ρ g).hom) ≫ _
      simp
    · change (normalizationMap f f _ _ (H h) ≫ normalizationMap f f _ _ (H g)) ≫ _ = _
      rw [map_mul]
      change _ = _ ≫ (σ h).hom ≫ (σ g).hom
      simp
section
variable (ρ : G →* Aut X) (σ : G →* Aut Y) (H : ∀ g, (ρ g).hom ≫ f = f ≫ (σ g).hom)
theorem normalizationAction_hom (g : G) :
    (normalizationAction f ρ σ H g).hom = normalizationMap f f (ρ g).hom (σ g).hom (H g) := rfl
@[reassoc (attr := simp)]
theorem toNormalization_normalizationAction (g : G) :
    f.toNormalization ≫ (normalizationAction f ρ σ H g).hom = (ρ g).hom ≫ f.toNormalization := by
  simp [normalizationAction_hom]
@[reassoc (attr := simp)]
theorem normalizationAction_fromNormalization (g : G) :
    (normalizationAction f ρ σ H g).hom ≫ f.fromNormalization =
      f.fromNormalization ≫ (σ g).hom := by
  simp [normalizationAction_hom]
end
noncomputable def normalizationActionOver (ρ : G →* Aut X) (H : ∀ g, (ρ g).hom ≫ f = f) :
    G →* Aut f.normalization :=
  normalizationAction f ρ 1 fun g ↦ (H g).trans (Category.comp_id f).symm
variable (ρ : G →* Aut X) (H : ∀ g, (ρ g).hom ≫ f = f)
@[reassoc (attr := simp)]
theorem toNormalization_normalizationActionOver (g : G) :
    f.toNormalization ≫ (normalizationActionOver f ρ H g).hom = (ρ g).hom ≫ f.toNormalization :=
  toNormalization_normalizationAction ..
@[reassoc (attr := simp)]
theorem normalizationActionOver_fromNormalization (g : G) :
    (normalizationActionOver f ρ H g).hom ≫ f.fromNormalization = f.fromNormalization :=
  (normalizationAction_fromNormalization ..).trans (Category.comp_id _)
end Action
section Invariants
variable {G : Type v} [Group G] {X X' Y : Scheme.{u}}
def IsInvariantSection (ρ : G →* Aut X) (U : X.Opens) (s : Γ(X, U)) : Prop :=
  ∀ g, ∃ h : U ≤ (ρ g).hom ⁻¹ᵁ U, (ρ g).hom.appLE U U h s = s
theorem preimage_le_of_invariant (ρ : G →* Aut X) (π : X ⟶ X') (hπ : ∀ g, (ρ g).hom ≫ π = π)
    (W : X'.Opens) (g : G) : π ⁻¹ᵁ W ≤ (ρ g).hom ⁻¹ᵁ π ⁻¹ᵁ W := by
  rw [← Scheme.Hom.comp_preimage, hπ]
theorem isInvariantSection_app (ρ : G →* Aut X) (π : X ⟶ X') (hπ : ∀ g, (ρ g).hom ≫ π = π)
    (W : X'.Opens) (t : Γ(X', W)) : IsInvariantSection ρ _ (π.app W t) := fun g ↦
  ⟨preimage_le_of_invariant ρ π hπ W g, by
    rw [← CommRingCat.comp_apply]
    simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, hπ]⟩
theorem IsInvariantSection.appLE {ρ : G →* Aut X} {τ : G →* Aut X'} (j : X ⟶ X')
    (hj : ∀ g, (ρ g).hom ≫ j = j ≫ (τ g).hom) {W : X'.Opens} {s : Γ(X', W)}
    (hs : IsInvariantSection τ W s) {U : X.Opens} (hU : ∀ g, U ≤ (ρ g).hom ⁻¹ᵁ U)
    (e : U ≤ j ⁻¹ᵁ W) : IsInvariantSection ρ U (j.appLE W U e s) := fun g ↦ by
  obtain ⟨h, hg⟩ := hs g
  refine ⟨hU g, ?_⟩
  conv_rhs => rw [← hg]
  simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, hj]
theorem IsInvariantSection.res {ρ : G →* Aut X} {W : X.Opens} {s : Γ(X, W)}
    (hs : IsInvariantSection ρ W s) {U : X.Opens} (hU : ∀ g, U ≤ (ρ g).hom ⁻¹ᵁ U) (e : U ≤ W) :
    IsInvariantSection ρ U (X.presheaf.map (homOfLE e).op s) :=
  hs.appLE (𝟙 X) (by simp) hU e
theorem IsInvariantSection.mem_range_app {ρ : G →* Aut X} (π : X ⟶ X') [QuasiCompact π]
    [IsSchemeTheoreticallyDominant π] (hπ : ∀ g, (ρ g).hom ≫ π = π)
    (hinv : ∀ W : X'.Opens, IsAffineOpen W → ∀ s : Γ(X, π ⁻¹ᵁ W),
      IsInvariantSection ρ _ s → s ∈ Set.range (π.app W))
    {W : X'.Opens} {s : Γ(X, π ⁻¹ᵁ W)} (hs : IsInvariantSection ρ _ s) :
    s ∈ Set.range (π.app W) :=
  mem_range_app_of_forall_isAffineOpen π W s fun V hV hVW ↦
    hinv V hV _ (hs.res (preimage_le_of_invariant ρ π hπ V) (π.preimage_mono hVW))
theorem IsInvariantSection.mem_range_app_basicOpen [Finite G] {ρ : G →* Aut X} (π : X ⟶ X')
    [QuasiCompact π] [QuasiSeparated π] (hπ : ∀ g, (ρ g).hom ≫ π = π) {W : X'.Opens}
    (hW : IsAffineOpen W)
    (hinv : ∀ s : Γ(X, π ⁻¹ᵁ W), IsInvariantSection ρ _ s → s ∈ Set.range (π.app W))
    (r : Γ(X', W)) {s : Γ(X, π ⁻¹ᵁ X'.basicOpen r)} (hs : IsInvariantSection ρ _ s) :
    s ∈ Set.range (π.app (X'.basicOpen r)) := by
  have hle : π ⁻¹ᵁ X'.basicOpen r ≤ π ⁻¹ᵁ W := π.preimage_mono (X'.basicOpen_le r)
  have hst := preimage_le_of_invariant ρ π hπ
  let := (X.presheaf.map (homOfLE hle).op).hom.toAlgebra
  have : IsLocalization.Away (π.app W r) Γ(X, π ⁻¹ᵁ X'.basicOpen r) := by
    have key : ∀ (U : X.Opens) (e : U = X.basicOpen (π.app W r)) (h : U ≤ π ⁻¹ᵁ W),
        letI := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
        IsLocalization.Away (π.app W r) Γ(X, U) := by
      rintro _ rfl h
      exact isLocalization_basicOpen_of_qcqs (π.isCompact_preimage hW.isCompact)
        (π.isQuasiSeparated_preimage hW.isQuasiSeparated) _
    exact key _ (π.preimage_basicOpen r) hle
  have hres (g : G) (b : Γ(X, π ⁻¹ᵁ W)) :
      algebraMap _ Γ(X, π ⁻¹ᵁ X'.basicOpen r) ((ρ g).hom.appLE _ _ (hst W g) b) =
        (ρ g).hom.appLE _ _ (hst _ g) (algebraMap _ Γ(X, π ⁻¹ᵁ X'.basicOpen r) b) := by
    simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map,
      Scheme.Hom.map_appLE]
  have hr (g : G) : (ρ g).hom.appLE _ _ (hst W g) (π.app W r) = π.app W r :=
    (isInvariantSection_app ρ π hπ W r g).2
  obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj (π.app W r) s
  have hm (g : G) : ∃ m : ℕ, π.app W r ^ m * (ρ g).hom.appLE _ _ (hst W g) b =
      π.app W r ^ m * b := by
    refine IsLocalization.Away.exists_of_eq (S := Γ(X, π ⁻¹ᵁ X'.basicOpen r)) _ ?_
    rw [hres, ← hb, map_mul, map_pow, ← hres, hr, (hs g).2]
  choose m hm using hm
  obtain ⟨M, hM⟩ := (Set.finite_range m).bddAbove
  obtain ⟨a, ha⟩ := hinv (π.app W r ^ M * b) fun g ↦ ⟨hst W g, by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (hM ⟨g, rfl⟩)
    rw [map_mul, map_pow, hr, pow_add, mul_assoc, hm, mul_assoc]⟩
  obtain ⟨w, hw⟩ : IsUnit (X'.presheaf.map (homOfLE (X'.basicOpen_le r)).op r) :=
    X'.toRingedSpace.isUnit_res_basicOpen r
  have hw' : π.app _ w = algebraMap _ Γ(X, π ⁻¹ᵁ X'.basicOpen r) (π.app W r) := by
    rw [hw]; exact app_presheaf_map_apply π _ r
  refine ⟨X'.presheaf.map (homOfLE (X'.basicOpen_le r)).op a * ↑(w⁻¹ ^ (M + n)), ?_⟩
  have hu : IsUnit (π.app (X'.basicOpen r) ↑(w ^ (M + n))) :=
    (Units.isUnit (w ^ (M + n))).map (π.app (X'.basicOpen r)).hom
  apply hu.mul_right_cancel
  rw [← map_mul, mul_assoc, ← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one, mul_one,
    app_presheaf_map_apply, ha, Units.val_pow_eq_pow_val, map_pow, hw']
  change algebraMap _ Γ(X, π ⁻¹ᵁ X'.basicOpen r) _ = _
  rw [map_mul, map_pow, ← hb]
  ring
theorem IsInvariantSection.mem_range_app_of_cover [Finite G] {ρ : G →* Aut X} (π : X ⟶ X')
    [QuasiCompact π] [QuasiSeparated π] [IsSchemeTheoreticallyDominant π]
    (hπ : ∀ g, (ρ g).hom ≫ π = π)
    (hinv : ∀ y : X', ∃ W : X'.Opens, IsAffineOpen W ∧ y ∈ W ∧ ∀ s : Γ(X, π ⁻¹ᵁ W),
      IsInvariantSection ρ _ s → s ∈ Set.range (π.app W))
    {W : X'.Opens} {s : Γ(X, π ⁻¹ᵁ W)} (hs : IsInvariantSection ρ _ s) :
    s ∈ Set.range (π.app W) :=
  mem_range_app_of_locally π W s fun y hy ↦ by
    obtain ⟨V, hV, hyV, h⟩ := hinv y
    obtain ⟨r, hr, hyr⟩ := hV.exists_basicOpen_le ⟨y, hy⟩ hyV
    exact ⟨_, hr, hyr, IsInvariantSection.mem_range_app_basicOpen π hπ hV h r
      (hs.res (preimage_le_of_invariant ρ π hπ _) (π.preimage_mono hr))⟩
@[reducible]
noncomputable def sectionsAction (ρ : G →* Aut X) (U : X.Opens)
    (hU : ∀ g, U ≤ (ρ g).hom ⁻¹ᵁ U) : MulSemiringAction G Γ(X, U) where
  smul g s := (ρ g⁻¹).hom.appLE U U (hU _) s
  one_smul s := by
    change (ρ 1⁻¹).hom.appLE U U (hU _) s = s
    have : (ρ 1⁻¹).hom = 𝟙 X := by rw [inv_one, map_one]; rfl
    simp only [this]
    exact congr($(X.presheaf.map_id (op U)) s)
  mul_smul g h s := by
    change (ρ (g * h)⁻¹).hom.appLE U U (hU _) s =
      (ρ g⁻¹).hom.appLE U U (hU _) ((ρ h⁻¹).hom.appLE U U (hU _) s)
    have : (ρ (g * h)⁻¹).hom = (ρ g⁻¹).hom ≫ (ρ h⁻¹).hom := by rw [mul_inv_rev, map_mul]; rfl
    simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, this]
  smul_zero g := map_zero _
  smul_add g := map_add _
  smul_one g := map_one _
  smul_mul g := map_mul _
theorem apply_eq_iff_exists_aut_of_invariant [Finite G] (ρ : G →* Aut X) (π : X ⟶ X')
    [IsAffineHom π] (hπ : ∀ g, (ρ g).hom ≫ π = π)
    (hinv : ∀ W : X'.Opens, IsAffineOpen W → ∀ s : Γ(X, π ⁻¹ᵁ W),
      IsInvariantSection ρ _ s → s ∈ Set.range (π.app W)) (x y : X) :
    π x = π y ↔ ∃ g, (ρ g).hom x = y := by
  refine ⟨fun hxy ↦ ?_, ?_⟩
  swap
  · rintro ⟨g, rfl⟩
    rw [← Scheme.Hom.comp_apply, hπ]
  obtain ⟨_, ⟨(W : X'.Opens), hW, rfl⟩, hx, -⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (π x)) isOpen_univ
  have hy : π y ∈ W := hxy ▸ hx
  have hW : IsAffineOpen W := hW
  have hU : IsAffineOpen (π ⁻¹ᵁ W) := hW.preimage π
  have hst := preimage_le_of_invariant ρ π hπ W
  let := sectionsAction ρ _ hst
  let := (π.app W).hom.toAlgebra
  have hfix (g : G) (a : Γ(X', W)) : g • algebraMap Γ(X', W) Γ(X, π ⁻¹ᵁ W) a = algebraMap _ _ a :=
    (isInvariantSection_app ρ π hπ W a g⁻¹).2
  have : SMulCommClass G Γ(X', W) Γ(X, π ⁻¹ᵁ W) := ⟨fun g a s ↦ by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hfix]⟩
  have : Algebra.IsInvariant Γ(X', W) Γ(X, π ⁻¹ᵁ W) G := ⟨fun s hs ↦
    hinv W hW s fun g ↦ ⟨hst g, by simpa only [inv_inv] using
      (show (ρ g⁻¹⁻¹).hom.appLE _ _ (hst _) s = s from hs g⁻¹)⟩⟩
  let P : Spec Γ(X, π ⁻¹ᵁ W) := hU.primeIdealOf ⟨x, hx⟩
  let Q : Spec Γ(X, π ⁻¹ᵁ W) := hU.primeIdealOf ⟨y, hy⟩
  have hP : hU.fromSpec P = x := hU.fromSpec_primeIdealOf ⟨x, hx⟩
  have hQ : hU.fromSpec Q = y := hU.fromSpec_primeIdealOf ⟨y, hy⟩
  have hPQ : Spec.map (π.app W) P = Spec.map (π.app W) Q := by
    apply hW.fromSpec.isOpenEmbedding.injective
    simp only [← Scheme.Hom.comp_apply, Scheme.Hom.app_eq_appLE,
      IsAffineOpen.SpecMap_appLE_fromSpec π hW hU]
    simp only [Scheme.Hom.comp_apply, hP, hQ, hxy]
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq Γ(X', W) Γ(X, π ⁻¹ᵁ W) G
    P.asIdeal Q.asIdeal congr($(hPQ).asIdeal)
  refine ⟨g, ?_⟩
  have : Spec.map ((ρ g).hom.appLE _ _ (hst g)) P = Q := by
    refine PrimeSpectrum.ext (Ideal.ext fun s ↦ ?_)
    rw [hg, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    change _ ↔ (ρ g⁻¹⁻¹).hom.appLE _ _ (hst _) s ∈ P.asIdeal
    simp only [inv_inv]
    rfl
  rw [← hP, ← hQ, ← this, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
    IsAffineOpen.SpecMap_appLE_fromSpec _ hU hU]
variable (f : X ⟶ Y) (f' : X' ⟶ Y) [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f']
  [QuasiSeparated f'] (π : X ⟶ X') (hf : π ≫ f' = f ≫ 𝟙 Y) (ρ : G →* Aut X)
  (hπ : ∀ g, (ρ g).hom ≫ π = π) (hρ : ∀ g, (ρ g).hom ≫ f = f)
include hπ in

@[reassoc]
theorem normalizationActionOver_normalizationMap (g : G) :
    (normalizationActionOver f ρ hρ g).hom ≫ normalizationMap f f' π (𝟙 Y) hf =
      normalizationMap f f' π (𝟙 Y) hf :=
  normalization_hom_ext f f'.fromNormalization (by simp [reassoc_of% hπ]) (by simp)
include hπ in

theorem mem_range_normalizationMap_app [QuasiCompact π] [IsSchemeTheoreticallyDominant π]
    (hinv : ∀ W : X'.Opens, IsAffineOpen W → ∀ s : Γ(X, π ⁻¹ᵁ W),
      IsInvariantSection ρ _ s → s ∈ Set.range (π.app W))
    (W : f'.normalization.Opens) (s : Γ(f.normalization, normalizationMap f f' π (𝟙 Y) hf ⁻¹ᵁ W))
    (hs : IsInvariantSection (normalizationActionOver f ρ hρ) _ s) :
    s ∈ Set.range ((normalizationMap f f' π (𝟙 Y) hf).app W) := by
  refine IsInvariantSection.mem_range_app _
    (normalizationActionOver_normalizationMap f f' π hf ρ hπ hρ) (fun W hW s hs ↦ ?_) hs
  have hq := toNormalization_normalizationMap f f' π (𝟙 Y) hf
  have : IsIntegralHom (normalizationMap f f' π (𝟙 Y) hf) := inferInstance
  generalize normalizationMap f f' π (𝟙 Y) hf = q at *
  have e : π ⁻¹ᵁ f'.toNormalization ⁻¹ᵁ W = f.toNormalization ⁻¹ᵁ q ⁻¹ᵁ W := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hq]
  let φ := f.toNormalization.appLE (q ⁻¹ᵁ W) (π ⁻¹ᵁ f'.toNormalization ⁻¹ᵁ W) e.le
  have hφ : Function.Injective φ := by
    have : ∀ (U : X.Opens) (e : U = f.toNormalization ⁻¹ᵁ q ⁻¹ᵁ W),
        Function.Injective (f.toNormalization.appLE (q ⁻¹ᵁ W) U e.le) := by
      rintro _ rfl
      rw [← Scheme.Hom.app_eq_appLE]
      exact f.toNormalization.app_injective _
    exact this _ e
  have hc : q.app W ≫ φ = f'.toNormalization.app W ≫ π.app _ := by
    simp only [φ, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, hq]
  obtain ⟨t, ht⟩ := IsInvariantSection.mem_range_app π hπ hinv
    (hs.appLE (ρ := ρ) f.toNormalization (by simp) (preimage_le_of_invariant ρ π hπ _) e.le)
  obtain ⟨a, rfl⟩ := mem_range_toNormalization_app f' W t (by
    obtain ⟨p, hp, h⟩ := q.isIntegral_app W hW s
    refine ⟨p, hp, π.app_injective _ ?_⟩
    have := congrArg φ.hom h
    rw [map_zero, Polynomial.hom_eval₂, ← CommRingCat.hom_comp, hc] at this
    rw [map_zero, Polynomial.hom_eval₂, ht]
    exact this)
  exact ⟨a, hφ (congr($hc a).trans ht)⟩
end Invariants
section Spec
variable (G : Type v) [Group G] (A B : Type u) [CommRing A] [CommRing B] [MulSemiringAction G B]
noncomputable def specAction : G →* Aut (Spec (.of B)) :=
  MonoidHom.mk' (fun g ↦
    { hom := Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G B g⁻¹))
      inv := Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G B g))
      hom_inv_id := by
        rw [← Spec.map_comp, ← Spec.map_id]; congr 1; ext b; simp
      inv_hom_id := by
        rw [← Spec.map_comp, ← Spec.map_id]; congr 1; ext b; simp }) fun g h ↦ by
    refine Iso.ext ?_
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext b
    simp [mul_smul]
theorem specAction_hom (g : G) : (specAction G B g).hom =
    Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G B g⁻¹)) := rfl
variable [Algebra A B]
theorem specAction_comp [SMulCommClass G A B] (g : G) :
    (specAction G B g).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) := by
  rw [specAction_hom, ← Spec.map_comp]
  congr 1
  ext a
  simp
theorem isSchemeTheoreticallyDominant_spec_algebraMap [FaithfulSMul A B] :
    IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  refine ⟨Scheme.IdealSheafData.ext_of_isAffine ?_⟩
  rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply,
    ← RingHom.injective_iff_ker_eq_bot]
  have := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A B))
  refine .of_comp (f := (Scheme.ΓSpecIso (.of B)).hom) fun x y h ↦ ?_
  exact (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.injective
    (FaithfulSMul.algebraMap_injective A B
      (congr($this x).symm.trans (h.trans congr($this y))))
theorem mem_range_spec_app_of_isInvariant [Finite G] [SMulCommClass G A B] [FaithfulSMul A B]
    [Algebra.IsInvariant A B G] (W : (Spec (.of A)).Opens)
    (s : Γ(Spec (.of B), Spec.map (CommRingCat.ofHom (algebraMap A B)) ⁻¹ᵁ W))
    (hs : IsInvariantSection (specAction G B) _ s) :
    s ∈ Set.range ((Spec.map (CommRingCat.ofHom (algebraMap A B))).app W) := by
  have := isSchemeTheoreticallyDominant_spec_algebraMap A B
  refine IsInvariantSection.mem_range_app_of_cover _ (specAction_comp G A B)
    (fun y ↦ ⟨⊤, isAffineOpen_top _, trivial, fun s hs ↦ ?_⟩) hs
  obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) (G := G)
    ((Scheme.ΓSpecIso (.of B)).hom s) fun g ↦ by
      have e := congr($(Scheme.ΓSpecIso_naturality
        (CommRingCat.ofHom (MulSemiringAction.toRingHom G B g⁻¹⁻¹))) s)
      have e' := congrArg (Scheme.ΓSpecIso (.of B)).hom (hs g⁻¹).2
      simpa only [inv_inv] using
        (show g⁻¹⁻¹ • (Scheme.ΓSpecIso (.of B)).hom s = _ from e.symm.trans e')
  refine ⟨(Scheme.ΓSpecIso (.of A)).inv a, ?_⟩
  refine congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A B))) a).symm.trans ?_
  change (Scheme.ΓSpecIso (.of B)).inv (algebraMap A B a) = s
  rw [ha]
  exact congr($((Scheme.ΓSpecIso (.of B)).hom_inv_id) s)
end Spec
theorem normalization_quotient {G : Type v} [Group G] [Finite G] {X X' Y : Scheme.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y) [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f']
    [QuasiSeparated f'] (π : X ⟶ X') (hf : π ≫ f' = f ≫ 𝟙 Y) (ρ : G →* Aut X)
    (hπ : ∀ g, (ρ g).hom ≫ π = π) (hρ : ∀ g, (ρ g).hom ≫ f = f)
    [IsSchemeTheoreticallyDominant π]
    (hinv : ∀ y : X', ∃ W : X'.Opens, IsAffineOpen W ∧ y ∈ W ∧ ∀ s : Γ(X, π ⁻¹ᵁ W),
      IsInvariantSection ρ _ s → s ∈ Set.range (π.app W)) :
    letI q := normalizationMap f f' π (𝟙 Y) hf
    letI τ := normalizationActionOver f ρ hρ
    (∀ g, (τ g).hom ≫ q = q) ∧ IsIntegralHom q ∧ Surjective q ∧
      (∀ x y, q x = q y ↔ ∃ g, (τ g).hom x = y) ∧
      ∀ W : f'.normalization.Opens, Function.Injective (q.app W) ∧
        Set.range (q.app W) = {s | IsInvariantSection τ (q ⁻¹ᵁ W) s} := by
  have : QuasiCompact (π ≫ f') := by rw [hf]; infer_instance
  have : QuasiSeparated (π ≫ f') := by rw [hf]; infer_instance
  have : QuasiCompact π := .of_comp π f'
  have : QuasiSeparated π := .of_comp π f'
  have h₁ := normalizationActionOver_normalizationMap f f' π hf ρ hπ hρ
  have h₂ := mem_range_normalizationMap_app f f' π hf ρ hπ hρ
    fun W _ s hs ↦ hs.mem_range_app_of_cover π hπ hinv
  refine ⟨h₁, inferInstance, inferInstance,
    apply_eq_iff_exists_aut_of_invariant _ _ h₁ fun W _ ↦ h₂ W,
    fun W ↦ ⟨Scheme.Hom.app_injective _ W, Set.ext fun s ↦ ⟨?_, h₂ W s⟩⟩⟩
  rintro ⟨t, rfl⟩
  exact isInvariantSection_app _ _ h₁ W t
theorem normalization_quotient_spec (G : Type v) [Group G] [Finite G] (R A B : Type u) [CommRing R]
    [CommRing A] [CommRing B] [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [MulSemiringAction G B] [SMulCommClass G A B] [SMulCommClass G R B] [FaithfulSMul A B]
    [Algebra.IsInvariant A B G] :
    letI q := normalizationMap (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (𝟙 _) (by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq,
        Category.comp_id])
    letI τ := normalizationActionOver _ (specAction G B) (specAction_comp G R B)
    (∀ g, (τ g).hom ≫ q = q) ∧ IsIntegralHom q ∧ Surjective q ∧
      (∀ x y, q x = q y ↔ ∃ g, (τ g).hom x = y) ∧
      ∀ W, Function.Injective (q.app W) ∧
        Set.range (q.app W) = {s | IsInvariantSection τ (q ⁻¹ᵁ W) s} :=
  have := isSchemeTheoreticallyDominant_spec_algebraMap A B
  normalization_quotient _ _ _ _ _ (specAction_comp G A B) _
    fun _ ↦ ⟨⊤, isAffineOpen_top _, trivial, mem_range_spec_app_of_isInvariant G A B ⊤⟩
example (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :=
  normalization_quotient_spec Gal(L/K) ℤ K L
end GlobalTheory


