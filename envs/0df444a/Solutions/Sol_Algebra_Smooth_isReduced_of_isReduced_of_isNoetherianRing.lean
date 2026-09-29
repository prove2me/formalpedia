-- Prove2me | solution 1 for Algebra.Smooth.isReduced_of_isReduced_of_isNoetherianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/bf8a3b32-3aa1-55c6-83dd-adf54d05b68f

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_Smooth_isReduced_of_isReduced_of_isNoetherianRing

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    [IsReduced R] [IsNoetherianRing R] : IsReduced S := by
  have hsm : AlgebraicGeometry.Smooth (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
    rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Smooth)]
    show (algebraMap R S).Smooth
    rw [RingHom.smooth_algebraMap]
    infer_instance
  have := AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian
    (Spec.map (CommRingCat.ofHom (algebraMap R S)))
  exact (affine_isReduced_iff (CommRingCat.of S)).mp this

end S_Algebra_Smooth_isReduced_of_isReduced_of_isNoetherianRing
end P2MW
export P2MW.S_Algebra_Smooth_isReduced_of_isReduced_of_isNoetherianRing (solution)
