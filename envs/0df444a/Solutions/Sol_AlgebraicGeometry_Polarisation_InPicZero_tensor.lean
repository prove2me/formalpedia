-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.InPicZero.tensor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/e4fc7770-2961-5f91-a7d2-d9d57a6c5ca1

import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_InPicZero_tensor

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) {M N : A.Modules} (hM : InPicZero f L M) (hN : InPicZero f L N) :
    InPicZero f L (M ⊗ N) := by
  refine ⟨Scheme.Modules.IsInvertible.tensor_monoidalV2 hM.1 hN.1, fun x => ?_⟩
  obtain ⟨eM⟩ := hM.2 x
  obtain ⟨eN⟩ := hN.2 x
  exact ⟨Scheme.Modules.pullbackTensorObjIso (L.translate x) M N ≪≫ (eM ⊗ᵢ eN)⟩

end S_AlgebraicGeometry_Polarisation_InPicZero_tensor
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_InPicZero_tensor (solution)
