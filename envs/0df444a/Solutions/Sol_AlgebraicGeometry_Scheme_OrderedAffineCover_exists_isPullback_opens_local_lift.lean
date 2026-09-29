-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.OrderedAffineCover.exists_isPullback_opens_local_lift
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/47874ab6-defa-59d6-b1b4-a2dabe1a4d73

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_isPullback_opens_local_lift

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u

theorem solution
    (T' T : Type u) [CommRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) [IsSeparated f₀]
    (𝒰 : A₀.OrderedAffineCover)
    (Y : 𝒰.ι → Scheme.{u}) (q : ∀ a, Y a ⟶ Spec (CommRingCat.of T')) (hq : ∀ a, Smooth (q a))
    (g : ∀ a, (↑(𝒰.U a) : Scheme.{u}) ⟶ Y a)
    (hg : ∀ a, IsPullback (g a) ((𝒰.U a).ι ≫ f₀) (q a) (Spec.map (CommRingCat.ofHom π)))

    (O : ∀ a, A₀.Opens → (Y a).Opens)
    (hO : ∀ (a : 𝒰.ι) (W : A₀.Opens), g a ⁻¹ᵁ O a W = (𝒰.U a).ι ⁻¹ᵁ W)
    (hOm : ∀ a, Monotone (O a))
    (hOtop : ∀ a, O a (𝒰.U a) = ⊤)
    (hOinf : ∀ (a : 𝒰.ι) (W W' : A₀.Opens), O a W ⊓ O a W' ≤ O a (W ⊓ W'))
    (hOaff : ∀ (a : 𝒰.ι) (W : A₀.Opens), IsAffineOpen W → W ≤ 𝒰.U a → IsAffineOpen (O a W))
    (a : 𝒰.ι) (W : A₀.Opens) (hWaff : IsAffineOpen W) (hW : W ≤ 𝒰.U a) :
    Smooth ((O a W).ι ≫ q a) ∧
    ∃ γ : (↑W : Scheme.{u}) ⟶ ↑(O a W),
      γ ≫ (O a W).ι = A₀.homOfLE hW ≫ g a ∧
      IsPullback γ (W.ι ≫ f₀) ((O a W).ι ≫ q a) (Spec.map (CommRingCat.ofHom π)) := by
  haveI := hq a
  refine ⟨inferInstance, ?_⟩

  have hrange : Set.range (A₀.homOfLE hW ≫ g a).base ⊆ Set.range (O a W).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    show (A₀.homOfLE hW ≫ g a).base x ∈ O a W
    rw [Scheme.Hom.comp_apply]
    have hx : (A₀.homOfLE hW).base x ∈ g a ⁻¹ᵁ O a W := by
      rw [hO]
      show ((𝒰.U a).ι.base ((A₀.homOfLE hW).base x)) ∈ W
      rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
      exact x.2
    exact hx
  obtain ⟨γ, hγ⟩ : ∃ γ : (↑W : Scheme.{u}) ⟶ ↑(O a W), γ ≫ (O a W).ι = A₀.homOfLE hW ≫ g a :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hrange⟩
  refine ⟨γ, hγ, ?_⟩

  have hK : IsPullback (g a ∣_ O a W) ((g a ⁻¹ᵁ O a W).ι ≫ (𝒰.U a).ι ≫ f₀) ((O a W).ι ≫ q a)
      (Spec.map (CommRingCat.ofHom π)) :=
    (isPullback_morphismRestrict (g a) (O a W)).paste_vert (hg a)

  have hrangeEq : Set.range ((g a ⁻¹ᵁ O a W).ι ≫ (𝒰.U a).ι).base = Set.range W.ι.base := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι, Scheme.Opens.range_ι, hO]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨y, hW hy⟩, hy, rfl⟩
  let e₁ : (↑(g a ⁻¹ᵁ O a W) : Scheme.{u}) ≅ ↑W :=
    IsOpenImmersion.isoOfRangeEq ((g a ⁻¹ᵁ O a W).ι ≫ (𝒰.U a).ι) W.ι hrangeEq
  have he₁ : e₁.hom ≫ W.ι = (g a ⁻¹ᵁ O a W).ι ≫ (𝒰.U a).ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have he₁' : e₁.hom ≫ A₀.homOfLE hW = (g a ⁻¹ᵁ O a W).ι := by
    rw [← cancel_mono (𝒰.U a).ι, Category.assoc, Scheme.homOfLE_ι, he₁]
  refine hK.of_iso e₁ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.comp_id, ← cancel_mono (O a W).ι, Category.assoc, hγ, morphismRestrict_ι,
      ← Category.assoc, he₁']
  · rw [Iso.refl_hom, Category.comp_id, reassoc_of% he₁]
  · simp
  · simp

end S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_isPullback_opens_local_lift
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_isPullback_opens_local_lift (solution)
