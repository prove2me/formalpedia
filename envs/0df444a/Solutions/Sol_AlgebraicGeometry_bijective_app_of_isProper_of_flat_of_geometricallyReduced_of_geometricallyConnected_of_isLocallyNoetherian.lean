-- Prove2me | solution 1 for AlgebraicGeometry.bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected_of_isLocallyNoetherian
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/51730436-e932-59ec-ba61-86c04965dd85

import Mathlib
import Theorems.Thm_AlgebraicGeometry_bijective_app_of_isProper_of_flat_of_forall_bijective_appTop_fiberToSpecResidueField_of_isLocallyNoetherian
import Theorems.Thm_AlgebraicGeometry_bijective_appTop_of_universallyClosed_of_geometricallyReduced_of_geometricallyConnected
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected_of_isLocallyNoetherian
p2m_attr_erase "instance" "AdicCompletion.instIsLocalRingMaximalIdeal"

open AlgebraicGeometry CategoryTheory

universe u

open CategoryTheory.Limits

theorem solution
    {X B : Scheme.{u}} [IsLocallyNoetherian B] (p : X ⟶ B) [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    [GeometricallyReduced p] [GeometricallyConnected p] (U : B.Opens) :
    Function.Bijective (p.app U) := by
  refine AlgebraicGeometry.bijective_app_of_isProper_of_flat_of_forall_bijective_appTop_fiberToSpecResidueField_of_isLocallyNoetherian
    p (fun b => ?_) U
  haveI : UniversallyClosed (pullback.snd p (B.fromSpecResidueField b)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  haveI : GeometricallyReduced (pullback.snd p (B.fromSpecResidueField b)) := inferInstance
  haveI : GeometricallyConnected (pullback.snd p (B.fromSpecResidueField b)) := inferInstance
  exact AlgebraicGeometry.bijective_appTop_of_universallyClosed_of_geometricallyReduced_of_geometricallyConnected
    (K := B.residueField b) (pullback.snd p (B.fromSpecResidueField b))

end S_AlgebraicGeometry_bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected_of_isLocallyNoetherian
end P2MW
export P2MW.S_AlgebraicGeometry_bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected_of_isLocallyNoetherian (solution)
