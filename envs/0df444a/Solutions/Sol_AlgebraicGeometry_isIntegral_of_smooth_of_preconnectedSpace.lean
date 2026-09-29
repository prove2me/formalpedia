-- Prove2me | solution 1 for AlgebraicGeometry.isIntegral_of_smooth_of_preconnectedSpace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/ed1e32a8-193d-5f12-8f65-ced1c9adecff

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk
import Theorems.Thm_IsRegularLocalRing_isDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [Smooth f] [PreconnectedSpace X] [Nonempty X] : IsIntegral X := by
  haveI : LocallyOfFiniteType f := inferInstance
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of k)) := inferInstance
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : ConnectedSpace X := { toPreconnectedSpace := inferInstance, toNonempty := inferInstance }
  exact AlgebraicGeometry.isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk X
    fun x => by
      haveI := AlgebraicGeometry.Smooth.isRegularLocalRing_stalk (f := f) x
      exact IsRegularLocalRing.isDomain _

end S_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace
end P2MW
export P2MW.S_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace (solution)
