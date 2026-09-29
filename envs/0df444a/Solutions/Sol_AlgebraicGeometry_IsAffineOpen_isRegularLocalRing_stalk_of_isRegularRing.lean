-- Prove2me | solution 1 for AlgebraicGeometry.IsAffineOpen.isRegularLocalRing_stalk_of_isRegularRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/9b3b1902-5196-5869-a75f-b1e3106c9da3

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_IsAffineOpen_isRegularLocalRing_stalk_of_isRegularRing

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (hreg : IsRegularRing Γ(X, U))
    (x : X) (hx : x ∈ U) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  haveI := hU.isLocalization_stalk ⟨x, hx⟩
  haveI := hreg
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
      (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal) (X.presheaf.stalk x)).toRingEquiv

end S_AlgebraicGeometry_IsAffineOpen_isRegularLocalRing_stalk_of_isRegularRing
end P2MW
export P2MW.S_AlgebraicGeometry_IsAffineOpen_isRegularLocalRing_stalk_of_isRegularRing (solution)
