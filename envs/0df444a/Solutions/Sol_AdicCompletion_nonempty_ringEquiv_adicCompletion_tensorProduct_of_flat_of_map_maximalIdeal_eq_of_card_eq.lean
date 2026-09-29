-- Prove2me | solution 1 for AdicCompletion.nonempty_ringEquiv_adicCompletion_tensorProduct_of_flat_of_map_maximalIdeal_eq_of_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/7648e2be-f4f2-55c8-b492-8fbad6298b13

import Mathlib
import Theorems.Thm_AdicCompletion_exists_moduleFinite_etale_adicCompletion_tensorProduct_of_flat_of_map_maximalIdeal_eq
import Theorems.Thm_AdicCompletion_finite_residueField_and_card_eq_of_isMaximal
import Theorems.Thm_Algebra_Etale_nonempty_algEquiv_of_isLocalRing_of_finite_residueField_of_card_eq
import Theorems.Thm_AdicCompletion_exists_isLocalRing_and_existsUnique_lift_of_isArtinianRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AdicCompletion_nonempty_ringEquiv_adicCompletion_tensorProduct_of_flat_of_map_maximalIdeal_eq_of_card_eq
p2m_attr_erase "instance" "AdicCompletion.instIsLocalRingMaximalIdeal"

set_option autoImplicit false

open IsLocalRing TensorProduct

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem solution
    (V : Type) [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    (D₁ : Type) [CommRing D₁] [IsLocalRing D₁] [Algebra V D₁] [IsLocalHom (algebraMap V D₁)] [Module.Flat V D₁]
    (hVD₁ : (maximalIdeal V).map (algebraMap V D₁) = maximalIdeal D₁)
    [Module.Finite (ResidueField V) (ResidueField D₁)] [Algebra.IsSeparable (ResidueField V) (ResidueField D₁)]
    (W : Type) [CommRing W] [IsLocalRing W] [IsNoetherianRing W]
    (D₂ : Type) [CommRing D₂] [IsLocalRing D₂] [Algebra W D₂] [IsLocalHom (algebraMap W D₂)] [Module.Flat W D₂]
    (hWD₂ : (maximalIdeal W).map (algebraMap W D₂) = maximalIdeal D₂)
    [Module.Finite (ResidueField W) (ResidueField D₂)] [Algebra.IsSeparable (ResidueField W) (ResidueField D₂)]
    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra V C] [Algebra W C]
    (𝔫 : Ideal C) [𝔫.IsMaximal] [Finite (C ⧸ 𝔫)]
    (h𝔫V : (maximalIdeal V).map (algebraMap V C) ≤ 𝔫) (h𝔫W : (maximalIdeal W).map (algebraMap W C) ≤ 𝔫)
    [IsNoetherianRing (C ⊗[V] D₁)] [IsNoetherianRing (C ⊗[W] D₂)]
    (x₁ : Ideal (C ⊗[V] D₁)) [x₁.IsMaximal] (hx₁ : 𝔫.map (algebraMap C (C ⊗[V] D₁)) ≤ x₁)
    (x₂ : Ideal (C ⊗[W] D₂)) [x₂.IsMaximal] (hx₂ : 𝔫.map (algebraMap C (C ⊗[W] D₂)) ≤ x₂)
    [Finite ((C ⊗[V] D₁) ⧸ x₁)] [Finite ((C ⊗[W] D₂) ⧸ x₂)]
    (hcard : Nat.card ((C ⊗[V] D₁) ⧸ x₁) = Nat.card ((C ⊗[W] D₂) ⧸ x₂)) :
    ∃ e : AdicCompletion x₁ (C ⊗[V] D₁) ≃+* AdicCompletion x₂ (C ⊗[W] D₂),
      ∀ c : C, e (algebraMap (C ⊗[V] D₁) (AdicCompletion x₁ (C ⊗[V] D₁)) (algebraMap C (C ⊗[V] D₁) c)) =
        algebraMap (C ⊗[W] D₂) (AdicCompletion x₂ (C ⊗[W] D₂)) (algebraMap C (C ⊗[W] D₂) c) := by
  classical

  obtain ⟨instR₀loc, instR₀noeth, instR₀cpl, -, -, -, -⟩ :=
    AdicCompletion.exists_isLocalRing_and_existsUnique_lift_of_isArtinianRing C 𝔫

  obtain ⟨_, instS₁loc, alg₁, tow₁, loc₁, fin₁, et₁, -⟩ :=
    AdicCompletion.exists_moduleFinite_etale_adicCompletion_tensorProduct_of_flat_of_map_maximalIdeal_eq
      V D₁ hVD₁ C 𝔫 h𝔫V x₁ hx₁
  obtain ⟨_, instS₂loc, alg₂, tow₂, loc₂, fin₂, et₂, -⟩ :=
    AdicCompletion.exists_moduleFinite_etale_adicCompletion_tensorProduct_of_flat_of_map_maximalIdeal_eq
      W D₂ hWD₂ C 𝔫 h𝔫W x₂ hx₂
  haveI := fin₁; haveI := fin₂; haveI := et₁; haveI := et₂; haveI := loc₁; haveI := loc₂

  obtain ⟨finκ₁, card₁⟩ := AdicCompletion.finite_residueField_and_card_eq_of_isMaximal (C ⊗[V] D₁) x₁ instS₁loc
  obtain ⟨finκ₂, card₂⟩ := AdicCompletion.finite_residueField_and_card_eq_of_isMaximal (C ⊗[W] D₂) x₂ instS₂loc
  haveI := finκ₁; haveI := finκ₂
  have hκ : Nat.card (ResidueField (AdicCompletion x₁ (C ⊗[V] D₁))) =
      Nat.card (ResidueField (AdicCompletion x₂ (C ⊗[W] D₂))) := by rw [card₁, card₂, hcard]

  obtain ⟨e⟩ := Algebra.Etale.nonempty_algEquiv_of_isLocalRing_of_finite_residueField_of_card_eq
    (AdicCompletion 𝔫 C) (AdicCompletion x₁ (C ⊗[V] D₁)) (AdicCompletion x₂ (C ⊗[W] D₂)) hκ
  refine ⟨e.toRingEquiv, fun c => ?_⟩
  have h1 : algebraMap (C ⊗[V] D₁) (AdicCompletion x₁ (C ⊗[V] D₁)) (algebraMap C (C ⊗[V] D₁) c) =
      algebraMap (AdicCompletion 𝔫 C) (AdicCompletion x₁ (C ⊗[V] D₁)) (algebraMap C (AdicCompletion 𝔫 C) c) := by
    rw [← IsScalarTower.algebraMap_apply C (AdicCompletion 𝔫 C)]
    simp [AdicCompletion.algebraMap_apply]
  have h2 : algebraMap (C ⊗[W] D₂) (AdicCompletion x₂ (C ⊗[W] D₂)) (algebraMap C (C ⊗[W] D₂) c) =
      algebraMap (AdicCompletion 𝔫 C) (AdicCompletion x₂ (C ⊗[W] D₂)) (algebraMap C (AdicCompletion 𝔫 C) c) := by
    rw [← IsScalarTower.algebraMap_apply C (AdicCompletion 𝔫 C)]
    simp [AdicCompletion.algebraMap_apply]
  rw [h1, h2]
  exact e.commutes _

end S_AdicCompletion_nonempty_ringEquiv_adicCompletion_tensorProduct_of_flat_of_map_maximalIdeal_eq_of_card_eq
end P2MW
export P2MW.S_AdicCompletion_nonempty_ringEquiv_adicCompletion_tensorProduct_of_flat_of_map_maximalIdeal_eq_of_card_eq (solution)
