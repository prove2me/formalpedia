-- Prove2me | solution 1 for AlgebraicGeometry.geometricallyIntegral_of_smooth_of_geometricallyConnected
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/04bb132e-d046-507f-a471-69c09a48da0f

import Mathlib
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk
import Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
import Theorems.Thm_IsRegularLocalRing_isDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_geometricallyIntegral_of_smooth_of_geometricallyConnected
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GeomIntKit

theorem isIntegral_of_smooth_of_connectedSpace {K : Type u} [Field K] {X : Scheme.{u}}
    (t : X ⟶ Spec (CommRingCat.of K)) [Smooth t] [ConnectedSpace X] : IsIntegral X := by
  haveI : LocallyOfFiniteType t := inferInstance
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian t
  exact AlgebraicGeometry.isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk
    X fun x => by
      haveI := AlgebraicGeometry.Smooth.isRegularLocalRing_stalk (f := t) x
      exact IsRegularLocalRing.isDomain _

end GeomIntKit

open GeomIntKit in
theorem solution
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] [GeometricallyConnected f] :
    GeometricallyIntegral f := by
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  haveI : Smooth (pullback.snd f y) := MorphismProperty.pullback_snd (P := @Smooth) _ _ ‹_›
  haveI : ConnectedSpace ↥(pullback f y) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd f y)
  haveI : IsIntegral (pullback f y) := isIntegral_of_smooth_of_connectedSpace (pullback.snd f y)
  exact IsIntegral.of_isIso h.isoPullback.inv

#print axioms solution

end S_AlgebraicGeometry_geometricallyIntegral_of_smooth_of_geometricallyConnected
end P2MW
export P2MW.S_AlgebraicGeometry_geometricallyIntegral_of_smooth_of_geometricallyConnected (solution)
