-- Prove2me | solution 1 for AlgebraicGeometry.isHomeomorph_of_isPullback_of_surjective_of_isNilpotent_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/ffc74d8c-47a5-53e9-92c3-9bbd9a17bc57

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isHomeomorph_of_isPullback_of_surjective_of_isNilpotent_ker

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem solution
    {B B₀ : Type u} [CommRing B] [CommRing B₀] (φ : B →+* B₀)
    (hφ : Function.Surjective φ) (hker : IsNilpotent (RingHom.ker φ))
    {X X₀ : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (f₀ : X₀ ⟶ Spec (CommRingCat.of B₀))
    (g : X₀ ⟶ X) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom φ))) :
    IsClosedImmersion g ∧ Surjective g ∧ IsHomeomorph g.base := by

  have hci : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ)) :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom φ) hφ

  have hsj : Surjective (Spec.map (CommRingCat.ofHom φ)) := by
    refine ⟨?_⟩
    rw [← Set.range_eq_univ]
    change Set.range (PrimeSpectrum.comap φ) = Set.univ
    rw [range_comap_of_surjective _ φ hφ, Set.eq_univ_iff_forall]
    intro p
    rw [PrimeSpectrum.mem_zeroLocus]
    intro x hx
    obtain ⟨n, hn⟩ := hker
    have hxn : IsNilpotent x := by
      refine ⟨n, ?_⟩
      have := Ideal.pow_mem_pow hx n
      rw [hn] at this
      simpa using this
    exact nilpotent_iff_mem_prime.mp hxn p.asIdeal inferInstance
  have h1 : IsClosedImmersion g := MorphismProperty.of_isPullback hg.flip hci
  have h2 : Surjective g := MorphismProperty.of_isPullback hg.flip hsj
  have h3 : IsHomeomorph g.base :=
    isHomeomorph_iff_isEmbedding_surjective.mpr ⟨g.isClosedEmbedding.isEmbedding, g.surjective⟩
  exact ⟨h1, h2, h3⟩

end S_AlgebraicGeometry_isHomeomorph_of_isPullback_of_surjective_of_isNilpotent_ker
end P2MW
export P2MW.S_AlgebraicGeometry_isHomeomorph_of_isPullback_of_surjective_of_isNilpotent_ker (solution)
