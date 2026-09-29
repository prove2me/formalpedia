-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.isIso_fromTildeGamma_of_locallyTrivial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/1423a37d-9b4a-57a1-bd9d-b841e380e652

import Mathlib.AlgebraicGeometry.Modules.Tilde
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_of_isLocalization_basicOpen
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_locallyTrivial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_of_locallyTrivial

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {R : CommRingCat.{u}} (M : (Spec (.of R)).Modules)
    (htriv : ∀ x : Spec (.of R), ∃ (V : (Spec (.of R)).Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)) :
    IsIso M.fromTildeΓ :=
  AlgebraicGeometry.Scheme.Modules.isIso_fromTildeGamma_of_isLocalization_basicOpen M fun g =>
    AlgebraicGeometry.Scheme.Modules.isLocalization_basicOpen_of_locallyTrivial M htriv
      ⟨⊤, isAffineOpen_top (Spec (.of R))⟩ g

end S_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_of_locallyTrivial
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_of_locallyTrivial (solution)
