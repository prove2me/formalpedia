-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/0f8ca974-e4e1-575e-90a9-a0bdea381a5f

import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.AffineScheme
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_locallyTrivial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) (M : V.Modules)
    (htriv : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)) :
    (OModulePresheaf.ofModules π M).IsQuasicoherent :=
  fun U f => Scheme.Modules.isLocalization_basicOpen_of_locallyTrivial M htriv U f

end S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial (solution)
