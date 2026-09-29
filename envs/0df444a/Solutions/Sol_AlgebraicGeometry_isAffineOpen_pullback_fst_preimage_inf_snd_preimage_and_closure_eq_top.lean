-- Prove2me | solution 1 for AlgebraicGeometry.isAffineOpen_pullback_fst_preimage_inf_snd_preimage_and_closure_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/91503951-4beb-53ea-b519-77d3f0a02ce6

import Mathlib
import Theorems.Thm_AlgebraicGeometry_isAffineOpen_pullback_fst_preimage_inf_snd_preimage
import Theorems.Thm_AlgebraicGeometry_closure_range_pullback_fst_appTop_union_range_snd_appTop_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isAffineOpen_pullback_fst_preimage_inf_snd_preimage_and_closure_eq_top

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

namespace AffineProductAssembly

theorem appLE_congrHom {X Y : Scheme.{u}} {k k' : X ⟶ Y} (e : k = k') (U : Y.Opens) (V : X.Opens)
    (h : V ≤ k ⁻¹ᵁ U) (h' : V ≤ k' ⁻¹ᵁ U) : k.appLE U V h = k'.appLE U V h' := by
  subst e; rfl

theorem closure_union_range_eq_top_of_injective {Γ Γ' A B : Type*} [CommRing Γ] [CommRing Γ'] [CommRing A] [CommRing B]
    (E : Γ →+* Γ') (hE : Function.Injective E) (F₁ : A → Γ) (F₂ : B → Γ) (X₁ X₂ : Set Γ')
    (h₁ : E '' Set.range F₁ = X₁) (h₂ : E '' Set.range F₂ = X₂) (h : Subring.closure (X₁ ∪ X₂) = ⊤) :
    Subring.closure (Set.range F₁ ∪ Set.range F₂) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : E x ∈ Subring.map E (Subring.closure (Set.range F₁ ∪ Set.range F₂)) := by
    rw [RingHom.map_closure, Set.image_union, h₁, h₂, h]; trivial
  obtain ⟨y, hy, hyx⟩ := Subring.mem_map.1 hx
  exact hE hyx ▸ hy

theorem fromSpec_appLE_eq {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (h : (⊤ : (Spec Γ(X, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ h = (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  have key : ∀ {A B : (Spec Γ(X, U)).Opensᵒᵖ} (i j : A ⟶ B), i = j := fun i j => Subsingleton.elim i j
  rw [key (_ ≫ _) (𝟙 (Opposite.op ⊤)), CategoryTheory.Functor.map_id, Category.comp_id]

end AffineProductAssembly

open AffineProductAssembly in
theorem solution
    {X Y S : Scheme.{u}} [IsAffine S] (f : X ⟶ S) (g : Y ⟶ S)
    {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsAffineOpen V) :
    IsAffineOpen (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) ∧
    Subring.closure
      (Set.range (fun s : Γ(X, U) =>
          (pullback f g).presheaf.map
            (homOfLE (inf_le_left : pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V ≤ pullback.fst f g ⁻¹ᵁ U)).op
            ((pullback.fst f g).app U s)) ∪
        Set.range (fun t : Γ(Y, V) =>
          (pullback f g).presheaf.map
            (homOfLE (inf_le_right : pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V ≤ pullback.snd f g ⁻¹ᵁ V)).op
            ((pullback.snd f g).app V t))) = ⊤ := by
  classical
  let a := hU.fromSpec ≫ f
  let b := hV.fromSpec ≫ g
  let φ := pullback.map a b f g hU.fromSpec hV.fromSpec (𝟙 S) (by simp [a]) (by simp [b])
  have hrange : Scheme.Hom.opensRange φ = pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V := by
    ext x
    show x ∈ Set.range φ ↔ x ∈ ((pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V : (pullback f g).Opens) : Set _)
    rw [Scheme.Pullback.range_map, IsAffineOpen.range_fromSpec, IsAffineOpen.range_fromSpec]
    rfl
  refine ⟨AlgebraicGeometry.isAffineOpen_pullback_fst_preimage_inf_snd_preimage f g hU hV, ?_⟩
  set W := pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V with hWdef
  have hWeq : W = φ ''ᵁ ⊤ := by rw [Scheme.Hom.image_top_eq_opensRange, hrange]
  have hle : (⊤ : (pullback a b).Opens) ≤ φ ⁻¹ᵁ W := by
    rw [hWeq, Scheme.Hom.preimage_image_eq]

  let ψ := φ.appLE W ⊤ hle
  have hψ : Function.Bijective ψ := by
    apply (Scheme.Hom.appLE_congr φ hle hWeq rfl (fun k => Function.Bijective k)).2
    show Function.Bijective (φ.appLE (φ ''ᵁ ⊤) ⊤ (Scheme.Hom.preimage_image_eq φ ⊤).ge)
    rw [← Scheme.Hom.appIso_hom']
    exact ConcreteCategory.bijective_of_isIso _
  have hUle : (⊤ : (Spec Γ(X, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U := by rw [IsAffineOpen.fromSpec_preimage_self]
  have hVle : (⊤ : (Spec Γ(Y, V)).Opens) ≤ hV.fromSpec ⁻¹ᵁ V := by rw [IsAffineOpen.fromSpec_preimage_self]
  have hφ1 : φ ≫ pullback.fst f g = pullback.fst a b ≫ hU.fromSpec := by
    show pullback.lift _ _ _ ≫ _ = _; rw [pullback.lift_fst]
  have hφ2 : φ ≫ pullback.snd f g = pullback.snd a b ≫ hV.fromSpec := by
    show pullback.lift _ _ _ ≫ _ = _; rw [pullback.lift_snd]
  have hφU : (⊤ : (pullback a b).Opens) ≤ (pullback.fst a b ≫ hU.fromSpec) ⁻¹ᵁ U := by
    show ⊤ ≤ pullback.fst a b ⁻¹ᵁ (hU.fromSpec ⁻¹ᵁ U)
    rw [IsAffineOpen.fromSpec_preimage_self]; exact le_top
  have hφV : (⊤ : (pullback a b).Opens) ≤ (pullback.snd a b ≫ hV.fromSpec) ⁻¹ᵁ V := by
    show ⊤ ≤ pullback.snd a b ⁻¹ᵁ (hV.fromSpec ⁻¹ᵁ V)
    rw [IsAffineOpen.fromSpec_preimage_self]; exact le_top

  have key1 : ∀ s : Γ(X, U), ψ ((pullback.fst f g).appLE U W inf_le_left s) =
      (pullback.fst a b).appTop ((Scheme.ΓSpecIso Γ(X, U)).inv s) := by
    intro s
    have m1 := Scheme.Hom.appLE_comp_appLE φ (pullback.fst f g) U W ⊤ inf_le_left hle
    have m2 : (φ ≫ pullback.fst f g).appLE U ⊤ (by rw [hφ1]; exact hφU) =
        (pullback.fst a b ≫ hU.fromSpec).appLE U ⊤ hφU := appLE_congrHom hφ1 U ⊤ _ _
    have m3 := Scheme.Hom.appLE_comp_appLE (pullback.fst a b) hU.fromSpec U ⊤ ⊤ hUle le_top
    have m4 : (pullback.fst a b).appLE ⊤ ⊤ le_top = (pullback.fst a b).appTop := Scheme.Hom.appLE_eq_app _
    calc ψ ((pullback.fst f g).appLE U W inf_le_left s)
        = ((pullback.fst f g).appLE U W inf_le_left ≫ ψ) s := rfl
      _ = ((pullback.fst a b ≫ hU.fromSpec).appLE U ⊤ hφU) s := by rw [show ψ = φ.appLE W ⊤ hle from rfl, m1, m2]
      _ = (hU.fromSpec.appLE U ⊤ hUle ≫ (pullback.fst a b).appLE ⊤ ⊤ le_top) s := by rw [m3]
      _ = (pullback.fst a b).appTop ((Scheme.ΓSpecIso Γ(X, U)).inv s) := by
          rw [CommRingCat.comp_apply, fromSpec_appLE_eq hU hUle, m4]
  have key2 : ∀ t : Γ(Y, V), ψ ((pullback.snd f g).appLE V W inf_le_right t) =
      (pullback.snd a b).appTop ((Scheme.ΓSpecIso Γ(Y, V)).inv t) := by
    intro t
    have m1 := Scheme.Hom.appLE_comp_appLE φ (pullback.snd f g) V W ⊤ inf_le_right hle
    have m2 : (φ ≫ pullback.snd f g).appLE V ⊤ (by rw [hφ2]; exact hφV) =
        (pullback.snd a b ≫ hV.fromSpec).appLE V ⊤ hφV := appLE_congrHom hφ2 V ⊤ _ _
    have m3 := Scheme.Hom.appLE_comp_appLE (pullback.snd a b) hV.fromSpec V ⊤ ⊤ hVle le_top
    have m4 : (pullback.snd a b).appLE ⊤ ⊤ le_top = (pullback.snd a b).appTop := Scheme.Hom.appLE_eq_app _
    calc ψ ((pullback.snd f g).appLE V W inf_le_right t)
        = ((pullback.snd f g).appLE V W inf_le_right ≫ ψ) t := rfl
      _ = ((pullback.snd a b ≫ hV.fromSpec).appLE V ⊤ hφV) t := by rw [show ψ = φ.appLE W ⊤ hle from rfl, m1, m2]
      _ = (hV.fromSpec.appLE V ⊤ hVle ≫ (pullback.snd a b).appLE ⊤ ⊤ le_top) t := by rw [m3]
      _ = (pullback.snd a b).appTop ((Scheme.ΓSpecIso Γ(Y, V)).inv t) := by
          rw [CommRingCat.comp_apply, fromSpec_appLE_eq hV hVle, m4]

  show Subring.closure (Set.range (fun s : Γ(X, U) => (pullback.fst f g).appLE U W inf_le_left s) ∪
    Set.range (fun t : Γ(Y, V) => (pullback.snd f g).appLE V W inf_le_right t)) = ⊤
  apply closure_union_range_eq_top_of_injective ψ.hom hψ.1 _ _
    (Set.range (pullback.fst a b).appTop) (Set.range (pullback.snd a b).appTop)
  · ext z; constructor
    · rintro ⟨_, ⟨s, rfl⟩, rfl⟩; exact ⟨_, (key1 s).symm⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨s, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso Γ(X, U)).inv).2 y
      exact ⟨_, ⟨s, rfl⟩, key1 s⟩
  · ext z; constructor
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩; exact ⟨_, (key2 t).symm⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨t, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso Γ(Y, V)).inv).2 y
      exact ⟨_, ⟨t, rfl⟩, key2 t⟩
  · exact AlgebraicGeometry.closure_range_pullback_fst_appTop_union_range_snd_appTop_eq_top a b

end S_AlgebraicGeometry_isAffineOpen_pullback_fst_preimage_inf_snd_preimage_and_closure_eq_top
end P2MW
export P2MW.S_AlgebraicGeometry_isAffineOpen_pullback_fst_preimage_inf_snd_preimage_and_closure_eq_top (solution)
