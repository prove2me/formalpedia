-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_opens_local_lift_eq_of_iso_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/3fb68069-7000-5357-879e-5978c2bb0182

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_preimage_opens_local_lift_eq_of_iso_comp_eq

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
    (a b : 𝒰.ι)
    (φ : ((↑(O a (𝒰.U a ⊓ 𝒰.U b)) : Scheme.{u}) ≅ ↑(O b (𝒰.U a ⊓ 𝒰.U b))))
    (γ : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O a (𝒰.U a ⊓ 𝒰.U b)))
    (γ' : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O b (𝒰.U a ⊓ 𝒰.U b)))
    (hγ : γ ≫ (O a (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_left ≫ g a)
    (hγ' : γ' ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_right ≫ g b)
    (hφγ : γ ≫ φ.hom = γ') (W : A₀.Opens) :
    φ.hom ⁻¹ᵁ ((O b (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O b W) = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O a W := by

  have hSpec : Surjective (Spec.map (CommRingCat.ofHom π)) := by
    refine (surjective_iff _).mpr ?_
    intro p
    have hp : p ∈ Set.range (PrimeSpectrum.comap π) := by
      rw [range_comap_of_surjective _ π hπ]
      change ((RingHom.ker π : Ideal T') : Set T') ⊆ ((p : PrimeSpectrum T').asIdeal : Set T')
      intro x hx
      obtain ⟨n, hn⟩ := hker
      have hxn : x ^ n ∈ (RingHom.ker π) ^ n := Ideal.pow_mem_pow hx n
      rw [hn] at hxn
      have hx0 : x ^ n = 0 := by simpa using hxn
      exact p.isPrime.mem_of_pow_mem n (by rw [hx0]; exact Ideal.zero_mem _)
    obtain ⟨q', hq'⟩ := hp
    exact ⟨q', hq'⟩
  have hga : Surjective (g a) := MorphismProperty.of_isPullback (P := @Surjective) (hg a).flip hSpec

  have hγsurj : Function.Surjective γ.base := by
    intro y
    obtain ⟨u, hu⟩ := Scheme.Hom.surjective (g a) ((O a (𝒰.U a ⊓ 𝒰.U b)).ι.base y)
    have hu' : u ∈ (g a) ⁻¹ᵁ O a (𝒰.U a ⊓ 𝒰.U b) := by
      show (g a).base u ∈ (O a (𝒰.U a ⊓ 𝒰.U b) : Set (Y a))
      rw [hu, ← Scheme.Opens.range_ι (O a (𝒰.U a ⊓ 𝒰.U b))]
      exact ⟨y, rfl⟩
    rw [hO] at hu'

    have hu'' : (𝒰.U a).ι.base u ∈ Set.range (𝒰.U a ⊓ 𝒰.U b).ι.base := by
      rw [Scheme.Opens.range_ι]; exact hu'
    obtain ⟨u₀, hu₀⟩ := hu''
    have hlift : (A₀.homOfLE (inf_le_left : 𝒰.U a ⊓ 𝒰.U b ≤ 𝒰.U a)).base u₀ = u := by
      apply Scheme.Hom.injective (𝒰.U a).ι
      rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι, hu₀]
    refine ⟨u₀, Scheme.Hom.injective (O a (𝒰.U a ⊓ 𝒰.U b)).ι ?_⟩
    rw [← Scheme.Hom.comp_apply, hγ, Scheme.Hom.comp_apply, hlift, hu]

  have key : ∀ A B : (↑(O a (𝒰.U a ⊓ 𝒰.U b)) : Scheme.{u}).Opens, γ ⁻¹ᵁ A = γ ⁻¹ᵁ B → A = B := by
    intro A B h
    have h' := congrArg (fun W : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}).Opens => (W : Set (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}))) h
    simp only [Scheme.Hom.coe_preimage] at h'
    exact SetLike.coe_injective ((Set.preimage_injective.mpr hγsurj) h')
  apply key
  have hL : γ ⁻¹ᵁ (φ.hom ⁻¹ᵁ ((O b (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O b W)) = (𝒰.U a ⊓ 𝒰.U b).ι ⁻¹ᵁ W := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hφγ, hγ', Scheme.Hom.comp_preimage, hO,
      ← Scheme.Hom.comp_preimage, Scheme.homOfLE_ι]
  have hR : γ ⁻¹ᵁ ((O a (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O a W) = (𝒰.U a ⊓ 𝒰.U b).ι ⁻¹ᵁ W := by
    rw [← Scheme.Hom.comp_preimage, hγ, Scheme.Hom.comp_preimage, hO, ← Scheme.Hom.comp_preimage, Scheme.homOfLE_ι]
  rw [hL, hR]

end S_AlgebraicGeometry_Scheme_OrderedAffineCover_preimage_opens_local_lift_eq_of_iso_comp_eq
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_preimage_opens_local_lift_eq_of_iso_comp_eq (solution)
