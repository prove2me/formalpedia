-- Prove2me | solution 1 for AlgebraicGeometry.eq_univ_of_isClopen_of_range_specMap_subset_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/3f47fd2f-d9ec-553c-bea0-cd5c93ef7429

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_eq_univ_of_isClopen_of_range_specMap_subset_of_injective

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {R₀ L : Type} [CommRing R₀] [CommRing L] (φ : R₀ →+* L) (hφ : Function.Injective φ)
    (W : Set ↥(Spec (CommRingCat.of R₀))) (hW : IsClopen W)
    (hWL : Set.range (Spec.map (CommRingCat.ofHom φ)).base ⊆ W) : W = Set.univ := by
  have hdense : DenseRange (Spec.map (CommRingCat.ofHom φ)).base :=
    (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).2
      (by rw [(RingHom.injective_iff_ker_eq_bot φ).1 hφ]; exact bot_le)
  apply Set.eq_univ_of_univ_subset
  rw [← hdense.closure_range]
  exact (hW.1.closure_subset_iff).2 hWL

end S_AlgebraicGeometry_eq_univ_of_isClopen_of_range_specMap_subset_of_injective
end P2MW
export P2MW.S_AlgebraicGeometry_eq_univ_of_isClopen_of_range_specMap_subset_of_injective (solution)
