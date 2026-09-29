-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.isInvertible_tilde_of_projective_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/9eaa8d22-b86b-568b-8133-67c1809ed7d9

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_one_iff_isInvertible
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_tilde
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isInvertible_tilde_of_projective_rankOne
p2m_attr_erase "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

theorem solution {R : CommRingCat.{u}} (P : ModuleCat.{u} R) [Module.Finite R P] [Module.Projective R P]
    (hrk : ∀ (K : Type u) [Field K] [Algebra R K], Module.finrank K (K ⊗[R] P) = 1) :
    Scheme.Modules.IsInvertible (tilde P) :=
  (AlgebraicGeometry.Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible (tilde P)).mp
    (AlgebraicGeometry.Scheme.Modules.isLocallyFreeOfRank_tilde P 1 hrk)

end S_AlgebraicGeometry_Scheme_Modules_isInvertible_tilde_of_projective_rankOne
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_isInvertible_tilde_of_projective_rankOne (solution)
