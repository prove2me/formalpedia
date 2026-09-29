-- Prove2me | solution 1 for AlgebraicGeometry.exists_comp_openInclusion_eq_openInclusion_comp_of_local_lift
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/e61fc2ff-a50c-535b-a373-42ba9fc11981

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_comp_openInclusion_eq_openInclusion_comp_of_local_lift

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem CAux.surjective_specMap {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (hnil : ∀ x ∈ RingHom.ker f, IsNilpotent x) :
    Surjective (Spec.map (CommRingCat.ofHom f)) := by
  refine ⟨fun x => ?_⟩
  have hx : x ∈ Set.range (PrimeSpectrum.comap f) := by
    rw [range_comap_of_surjective _ f hf]
    refine (PrimeSpectrum.mem_zeroLocus x _).mpr ?_
    intro t ht
    obtain ⟨n, hn⟩ := hnil t ht
    exact x.2.mem_of_pow_mem n (by rw [hn]; exact x.asIdeal.zero_mem)
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, hy⟩

theorem solution
    {T' T : Type u} [CommRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    {A₀ X₀ Y Z : Scheme.{u}}
    (U : A₀.Opens) (g : (U : Scheme.{u}) ⟶ Y)
    (O : A₀.Opens → Y.Opens) (hO : ∀ W : A₀.Opens, g ⁻¹ᵁ O W = U.ι ⁻¹ᵁ W)
    (fX₀ : X₀ ⟶ Spec (CommRingCat.of T))
    (V : X₀.Opens) (gZ : (V : Scheme.{u}) ⟶ Z) (qZ : Z ⟶ Spec (CommRingCat.of T'))
    (hgZ : IsPullback gZ (V.ι ≫ fX₀) qZ (Spec.map (CommRingCat.ofHom π)))
    (OX : X₀.Opens → Z.Opens) (hOX : ∀ W : X₀.Opens, gZ ⁻¹ᵁ OX W = V.ι ⁻¹ᵁ W)
    (h₀ : X₀ ⟶ A₀) (hV : V ≤ h₀ ⁻¹ᵁ U)
    (hZ : Z ⟶ Y) (hhZg : gZ ≫ hZ = X₀.homOfLE hV ≫ (h₀ ∣_ U) ≫ g)
    (WX : X₀.Opens) (WA : A₀.Opens) (hWW : WX ≤ h₀ ⁻¹ᵁ WA) :
    ∃ η : (↑(OX WX) : Scheme.{u}) ⟶ ↑(O WA), η ≫ (O WA).ι = (OX WX).ι ≫ hZ := by
  classical

  haveI : Surjective (Spec.map (CommRingCat.ofHom π)) := by
    refine CAux.surjective_specMap π hπ (fun x hx => ?_)
    obtain ⟨n, hn⟩ := hker
    refine ⟨n, ?_⟩
    have hx' : x ^ n ∈ RingHom.ker π ^ n := Ideal.pow_mem_pow hx n
    rw [hn] at hx'
    exact (Submodule.mem_bot _).mp hx'
  haveI : Surjective gZ := MorphismProperty.of_isPullback hgZ.flip inferInstance

  have hrange : Set.range ((OX WX).ι ≫ hZ).base ⊆ Set.range (O WA).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩

    obtain ⟨v, hv⟩ := gZ.surjective ((OX WX).ι.base z)
    have hvW : v ∈ (gZ ⁻¹ᵁ OX WX : Set _) := by
      show gZ.base v ∈ (OX WX : Set Z)
      rw [hv, ← Scheme.Opens.range_ι (OX WX)]; exact ⟨z, rfl⟩
    rw [hOX] at hvW

    have h1 : ((OX WX).ι ≫ hZ).base z = hZ.base (gZ.base v) := by
      rw [Scheme.Hom.comp_base, TopCat.comp_app, hv]
    rw [h1, ← TopCat.comp_app, ← Scheme.Hom.comp_base, hhZg]
    simp only [Scheme.Hom.comp_base, TopCat.comp_app]

    have h2 : (X₀.homOfLE hV ≫ (h₀ ∣_ U)).base v ∈ (g ⁻¹ᵁ O WA : Set _) := by
      rw [hO]
      show ((X₀.homOfLE hV ≫ (h₀ ∣_ U)) ≫ U.ι).base v ∈ (WA : Set A₀)
      rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.comp_base,
        TopCat.comp_app]
      exact hWW hvW
    simpa [Scheme.Hom.comp_base] using h2
  exact ⟨IsOpenImmersion.lift (O WA).ι ((OX WX).ι ≫ hZ) hrange, IsOpenImmersion.lift_fac _ _ _⟩

end S_AlgebraicGeometry_exists_comp_openInclusion_eq_openInclusion_comp_of_local_lift
end P2MW
export P2MW.S_AlgebraicGeometry_exists_comp_openInclusion_eq_openInclusion_comp_of_local_lift (solution)
