-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.OrderedAffineCover.exists_transitions_any_pair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/23d4fa53-ad6f-538e-b8d5-f6095a2b6349

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_iso_comp_homOfLE_eq_homOfLE_comp_of_preimage_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_transitions_any_pair

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {A₀ : Scheme.{u}} (𝒰 : A₀.OrderedAffineCover)
    {T' : Type u} [CommRing T']
    (Y : 𝒰.ι → Scheme.{u}) (q : ∀ a, Y a ⟶ Spec (CommRingCat.of T'))
    (g : ∀ a, (↑(𝒰.U a) : Scheme.{u}) ⟶ Y a)
    (O : ∀ a, A₀.Opens → (Y a).Opens) (hOm : ∀ a, Monotone (O a))
    (φ : ∀ (a b : 𝒰.ι), a < b → ((↑(O a (𝒰.U a ⊓ 𝒰.U b)) : Scheme.{u}) ≅ ↑(O b (𝒰.U a ⊓ 𝒰.U b))))
    (hφq : ∀ (a b : 𝒰.ι) (h : a < b),
      (φ a b h).hom ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q b = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q a)
    (hφg : ∀ (a b : 𝒰.ι) (h : a < b),
      ∃ (γ : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O a (𝒰.U a ⊓ 𝒰.U b)))
        (γ' : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O b (𝒰.U a ⊓ 𝒰.U b))),
        γ ≫ (O a (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_left ≫ g a ∧
        γ' ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_right ≫ g b ∧
        γ ≫ (φ a b h).hom = γ')
    (hφO : ∀ (a b : 𝒰.ι) (h : a < b) (W : A₀.Opens),
      (φ a b h).hom ⁻¹ᵁ ((O b (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O b W) = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O a W) :
    ∃ Φ : ∀ (a b : 𝒰.ι) (W : A₀.Opens), W ≤ 𝒰.U a → W ≤ 𝒰.U b → ((↑(O a W) : Scheme.{u}) ≅ ↑(O b W)),
      (∀ (a b : 𝒰.ι) (W : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b),
        (Φ a b W ha hb).hom ≫ (O b W).ι ≫ q b = (O a W).ι ≫ q a) ∧
      (∀ (a b : 𝒰.ι) (W : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b)
        (γ : (↑W : Scheme.{u}) ⟶ ↑(O a W)) (γ' : (↑W : Scheme.{u}) ⟶ ↑(O b W)),
        γ ≫ (O a W).ι = A₀.homOfLE ha ≫ g a → γ' ≫ (O b W).ι = A₀.homOfLE hb ≫ g b → γ ≫ (Φ a b W ha hb).hom = γ') ∧
      (∀ (a b : 𝒰.ι) (W W' : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b) (ha' : W' ≤ 𝒰.U a) (hb' : W' ≤ 𝒰.U b)
        (hWW : W' ≤ W),
        (Φ a b W' ha' hb').hom ≫ (Y b).homOfLE (hOm b hWW) = (Y a).homOfLE (hOm a hWW) ≫ (Φ a b W ha hb).hom) ∧
      (∀ (a : 𝒰.ι) (W : A₀.Opens) (ha ha' : W ≤ 𝒰.U a), (Φ a a W ha ha').hom = 𝟙 _) ∧
      (∀ (a b : 𝒰.ι) (W : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b),
        (Φ a b W ha hb).hom ≫ (Φ b a W hb ha).hom = 𝟙 _) ∧
      (∀ (a b : 𝒰.ι) (h : a < b),
        (Φ a b (𝒰.U a ⊓ 𝒰.U b) inf_le_left inf_le_right).hom = (φ a b h).hom) := by
  classical

  have hτ : ∀ (a b : 𝒰.ι) (h : a < b) (W : A₀.Opens) (hW : W ≤ 𝒰.U a ⊓ 𝒰.U b),
      ∃ τ : (↑(O a W) : Scheme.{u}) ≅ ↑(O b W),
        τ.hom ≫ (Y b).homOfLE (hOm b hW) = (Y a).homOfLE (hOm a hW) ≫ (φ a b h).hom ∧
        τ.inv ≫ (Y a).homOfLE (hOm a hW) = (Y b).homOfLE (hOm b hW) ≫ (φ a b h).inv :=
    fun a b h W hW => AlgebraicGeometry.Scheme.exists_iso_comp_homOfLE_eq_homOfLE_comp_of_preimage_eq
      (O a (𝒰.U a ⊓ 𝒰.U b)) (O b (𝒰.U a ⊓ 𝒰.U b)) (φ a b h) (O a W) (O b W) (hOm a hW) (hOm b hW) (hφO a b h W)
  choose τ hτ₁ hτ₂ using hτ

  have hq_lt : ∀ (a b : 𝒰.ι) (hab : a < b) (W : A₀.Opens) (hW : W ≤ 𝒰.U a ⊓ 𝒰.U b),
      (τ a b hab W hW).hom ≫ (O b W).ι ≫ q b = (O a W).ι ≫ q a := by
    intro a b hab W hW
    rw [← Scheme.homOfLE_ι _ (hOm b hW)]
    simp only [Category.assoc]
    rw [← Category.assoc, hτ₁ a b hab W hW]
    simp only [Category.assoc]
    rw [hφq, ← Category.assoc, Scheme.homOfLE_ι]
  have hq_gt : ∀ (a b : 𝒰.ι) (hba : b < a) (W : A₀.Opens) (hW : W ≤ 𝒰.U b ⊓ 𝒰.U a),
      (τ b a hba W hW).inv ≫ (O b W).ι ≫ q b = (O a W).ι ≫ q a := by
    intro a b hba W hW
    rw [← Scheme.homOfLE_ι _ (hOm b hW)]
    simp only [Category.assoc]
    rw [← Category.assoc, hτ₂ b a hba W hW]
    simp only [Category.assoc]
    rw [← hφq b a hba, Iso.inv_hom_id_assoc, ← Category.assoc, Scheme.homOfLE_ι]

  have hg_lt : ∀ (a b : 𝒰.ι) (hab : a < b) (W : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b)
      (γ : (↑W : Scheme.{u}) ⟶ ↑(O a W)) (γ' : (↑W : Scheme.{u}) ⟶ ↑(O b W)),
      γ ≫ (O a W).ι = A₀.homOfLE ha ≫ g a → γ' ≫ (O b W).ι = A₀.homOfLE hb ≫ g b →
      γ ≫ (τ a b hab W (le_inf ha hb)).hom = γ' := by
    intro a b hab W ha hb γ γ' hγ hγ'
    obtain ⟨γ₀, γ₀', h₀, h₀', hφ₀⟩ := hφg a b hab
    have e1 : γ ≫ (Y a).homOfLE (hOm a (le_inf ha hb)) = A₀.homOfLE (le_inf ha hb) ≫ γ₀ := by
      rw [← cancel_mono (O a (𝒰.U a ⊓ 𝒰.U b)).ι]
      simp only [Category.assoc, Scheme.homOfLE_ι, h₀]
      rw [hγ, ← Category.assoc, Scheme.homOfLE_homOfLE]
    rw [← cancel_mono (O b W).ι, ← Scheme.homOfLE_ι _ (hOm b (le_inf ha hb)), Category.assoc,
      ← Category.assoc (τ a b hab W _).hom, hτ₁ a b hab W (le_inf ha hb), Category.assoc, ← Category.assoc γ, e1,
      Category.assoc, ← Category.assoc γ₀, hφ₀, h₀', Scheme.homOfLE_ι, hγ', ← Category.assoc, Scheme.homOfLE_homOfLE]

  have hres_lt : ∀ (a b : 𝒰.ι) (hab : a < b) (W W' : A₀.Opens) (hW : W ≤ 𝒰.U a ⊓ 𝒰.U b)
      (hW' : W' ≤ 𝒰.U a ⊓ 𝒰.U b) (hWW : W' ≤ W),
      (τ a b hab W' hW').hom ≫ (Y b).homOfLE (hOm b hWW) = (Y a).homOfLE (hOm a hWW) ≫ (τ a b hab W hW).hom := by
    intro a b hab W W' hW hW' hWW
    rw [← cancel_mono ((Y b).homOfLE (hOm b hW)), Category.assoc, Category.assoc, Scheme.homOfLE_homOfLE,
      hτ₁ a b hab W hW, hτ₁ a b hab W' hW', ← Category.assoc, Scheme.homOfLE_homOfLE]
  have hres_gt : ∀ (a b : 𝒰.ι) (hba : b < a) (W W' : A₀.Opens) (hW : W ≤ 𝒰.U b ⊓ 𝒰.U a)
      (hW' : W' ≤ 𝒰.U b ⊓ 𝒰.U a) (hWW : W' ≤ W),
      (τ b a hba W' hW').inv ≫ (Y b).homOfLE (hOm b hWW) = (Y a).homOfLE (hOm a hWW) ≫ (τ b a hba W hW).inv := by
    intro a b hba W W' hW hW' hWW
    rw [← cancel_mono ((Y b).homOfLE (hOm b hW)), Category.assoc, Category.assoc, Scheme.homOfLE_homOfLE,
      hτ₂ b a hba W hW, hτ₂ b a hba W' hW', ← Category.assoc, Scheme.homOfLE_homOfLE]

  refine ⟨fun a b W ha hb =>
      if hab : a < b then τ a b hab W (le_inf ha hb)
      else if hba : b < a then (τ b a hba W (le_inf hb ha)).symm
      else eqToIso (by obtain rfl : a = b := le_antisymm (not_lt.mp hba) (not_lt.mp hab); rfl),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro a b W ha hb
    dsimp only
    by_cases hab : a < b
    · rw [dif_pos hab]; exact hq_lt a b hab W (le_inf ha hb)
    · rw [dif_neg hab]
      by_cases hba : b < a
      · rw [dif_pos hba]; exact hq_gt a b hba W (le_inf hb ha)
      · rw [dif_neg hba]
        obtain rfl : a = b := le_antisymm (not_lt.mp hba) (not_lt.mp hab)
        simp
  ·
    intro a b W ha hb γ γ' hγ hγ'
    dsimp only
    by_cases hab : a < b
    · rw [dif_pos hab]; exact hg_lt a b hab W ha hb γ γ' hγ hγ'
    · rw [dif_neg hab]
      by_cases hba : b < a
      · rw [dif_pos hba, Iso.symm_hom, ← hg_lt b a hba W hb ha γ' γ hγ' hγ, Category.assoc, Iso.hom_inv_id,
          Category.comp_id]
      · rw [dif_neg hba]
        obtain rfl : a = b := le_antisymm (not_lt.mp hba) (not_lt.mp hab)
        have : γ = γ' := by rw [← cancel_mono (O a W).ι, hγ, hγ']
        simp [this]
  ·
    intro a b W W' ha hb ha' hb' hWW
    dsimp only
    by_cases hab : a < b
    · rw [dif_pos hab, dif_pos hab]; exact hres_lt a b hab W W' (le_inf ha hb) (le_inf ha' hb') hWW
    · rw [dif_neg hab, dif_neg hab]
      by_cases hba : b < a
      · rw [dif_pos hba, dif_pos hba, Iso.symm_hom, Iso.symm_hom]
        exact hres_gt a b hba W W' (le_inf hb ha) (le_inf hb' ha') hWW
      · rw [dif_neg hba, dif_neg hba]
        obtain rfl : a = b := le_antisymm (not_lt.mp hba) (not_lt.mp hab)
        simp
  ·
    intro a W ha ha'
    dsimp only
    rw [dif_neg (lt_irrefl a), dif_neg (lt_irrefl a)]
    simp
  ·
    intro a b W ha hb
    dsimp only
    by_cases hab : a < b
    · rw [dif_pos hab, dif_neg (lt_asymm hab), dif_pos hab, Iso.symm_hom, Iso.hom_inv_id]
    · rw [dif_neg hab]
      by_cases hba : b < a
      · rw [dif_pos hba, dif_pos hba, Iso.symm_hom, Iso.inv_hom_id]
      · rw [dif_neg hba, dif_neg hba, dif_neg hab]
        obtain rfl : a = b := le_antisymm (not_lt.mp hba) (not_lt.mp hab)
        simp
  ·
    intro a b h
    dsimp only
    rw [dif_pos h]
    have := hτ₁ a b h (𝒰.U a ⊓ 𝒰.U b) (le_inf inf_le_left inf_le_right)
    simpa using this

end S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_transitions_any_pair
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_transitions_any_pair (solution)
