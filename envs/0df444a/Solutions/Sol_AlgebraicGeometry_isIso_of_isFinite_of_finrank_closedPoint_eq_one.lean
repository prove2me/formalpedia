-- Prove2me | solution 1 for AlgebraicGeometry.isIso_of_isFinite_of_finrank_closedPoint_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/6086a9f4-5920-5f71-8908-44a0208254f9

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isIso_of_isFinite_of_finrank_closedPoint_eq_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    (K : Type) [Field K] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of K)) [IsFinite p]
    (h : p.finrank (IsLocalRing.closedPoint K) = 1) :
    IsIso p := by
  refine (Scheme.Hom.isIso_iff_finrank_eq p).mpr ?_
  funext s
  have hs : s = IsLocalRing.closedPoint K := by
    apply PrimeSpectrum.ext
    rw [Ideal.eq_bot_of_prime s.asIdeal]
    exact (Ideal.eq_bot_of_prime _).symm
  rw [hs, h]
  rfl

end S_AlgebraicGeometry_isIso_of_isFinite_of_finrank_closedPoint_eq_one
end P2MW
export P2MW.S_AlgebraicGeometry_isIso_of_isFinite_of_finrank_closedPoint_eq_one (solution)
