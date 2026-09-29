-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.quotientInvariants_pullback_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/4ecc2b23-5c9b-58f1-b20b-cd9cac19026f

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_app_injective_and_range_eq_invariants_of_isBasis
import Theorems.Thm_AlgebraicGeometry_Scheme_app_basicOpen_injective_and_range_eq_invariants_of_flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_quotientInvariants_pullback_of_flat

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {B₀ 𝒪 : Type} [CommRing B₀] [CommRing 𝒪] (i : B₀ →+* 𝒪) (hi : Flat (Spec.map (CommRingCat.ofHom i)))
    {M X : Scheme.{0}} (πM : M ⟶ Spec (CommRingCat.of B₀)) (πX : X ⟶ Spec (CommRingCat.of B₀))
    (π : M ⟶ X) (hπX : π ≫ πX = πM)
    {H : Type} [Group H] [Finite H] (ρ : H →* Aut M) (hover : ∀ h : H, (ρ h).hom ≫ πM = πM)
    (hπ : ∀ h : H, (ρ h).hom ≫ π = π)
    (hint : IsIntegralHom π) (haff : IsAffineHom π) (hsurj : Function.Surjective π.base)
    (hsec : ∀ V : X.Opens, Function.Injective (π.app V))
    (hinv : ∀ V : X.Opens, Set.range (π.app V) =
      {s | ∀ h : H, (ρ h).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ h]) s = s})

    {M' X' : Scheme.{0}} (πM' : M' ⟶ Spec (CommRingCat.of 𝒪)) (πX' : X' ⟶ Spec (CommRingCat.of 𝒪))
    (gM : M' ⟶ M) (hgM : IsPullback gM πM' πM (Spec.map (CommRingCat.ofHom i)))
    (gX : X' ⟶ X) (hgX : IsPullback gX πX' πX (Spec.map (CommRingCat.ofHom i)))
    (π' : M' ⟶ X') (hπX' : π' ≫ πX' = πM') (hπg : π' ≫ gX = gM ≫ π)
    (ρ' : H →* Aut M') (hover' : ∀ h : H, (ρ' h).hom ≫ πM' = πM') (hρg : ∀ h : H, (ρ' h).hom ≫ gM = gM ≫ (ρ h).hom)
    (hπ' : ∀ h : H, (ρ' h).hom ≫ π' = π') :
    IsIntegralHom π' ∧ IsAffineHom π' ∧ Function.Surjective π'.base ∧
    (∀ V' : X'.Opens, Function.Injective (π'.app V')) ∧
    (∀ V' : X'.Opens, Set.range (π'.app V') =
      {s | ∀ h : H, (ρ' h).hom.appLE (π' ⁻¹ᵁ V') (π' ⁻¹ᵁ V') (by rw [← Scheme.Hom.comp_preimage, hπ' h]) s = s}) := by
  set si := Spec.map (CommRingCat.ofHom i) with hsi

  have hsq : IsPullback gM π' π gX := by
    refine IsPullback.of_bot (h₃₁ := si) (v₂₁ := πX') (v₂₂ := πX) ?_ hπg.symm hgX
    rw [hπX', hπX]; exact hgM

  haveI : IsAffineHom gX := MorphismProperty.of_isPullback hgX.flip inferInstance
  let B : Set X'.Opens := {O | ∃ (V : X.Opens) (_ : IsAffineOpen V) (r : Γ(X', gX ⁻¹ᵁ V)), O = X'.basicOpen r}
  have hB : TopologicalSpace.Opens.IsBasis B := by
    rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
    intro O x hx
    obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := gX.base x) (U := ⊤) trivial
    have hW : IsAffineOpen (gX ⁻¹ᵁ V) := hV.preimage gX
    obtain ⟨r, hrO, hxr⟩ := hW.exists_basicOpen_le ⟨x, hx⟩ hxV
    exact ⟨X'.basicOpen r, ⟨V, hV, r, rfl⟩, hxr, hrO⟩
  obtain ⟨h4, h5⟩ := AlgebraicGeometry.Scheme.app_injective_and_range_eq_invariants_of_isBasis π' ρ' hπ' B hB
    (fun W hW => by
      obtain ⟨V, hV, r, rfl⟩ := hW
      exact (AlgebraicGeometry.Scheme.app_basicOpen_injective_and_range_eq_invariants_of_flat i hi πM πX π hπX ρ hover
        hπ hint haff hsurj hsec hinv πM' πX' gM hgM gX hgX π' hπX' hπg ρ' hover' hρg hπ' V hV r).1)
    (fun W hW => by
      obtain ⟨V, hV, r, rfl⟩ := hW
      exact (AlgebraicGeometry.Scheme.app_basicOpen_injective_and_range_eq_invariants_of_flat i hi πM πX π hπX ρ hover
        hπ hint haff hsurj hsec hinv πM' πX' gM hgM gX hgX π' hπX' hπg ρ' hover' hρg hπ' V hV r).2)
  exact ⟨MorphismProperty.of_isPullback hsq hint, MorphismProperty.of_isPullback hsq haff,
    (MorphismProperty.of_isPullback (P := @Surjective) hsq ⟨hsurj⟩).1, h4, h5⟩

end S_AlgebraicGeometry_Scheme_quotientInvariants_pullback_of_flat
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_quotientInvariants_pullback_of_flat (solution)
