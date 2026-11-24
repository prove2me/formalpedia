-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_isAffineOpen_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:57.917812+00:00
-- url     : https://prove2.me/submissions/113cfe97-96db-4d0d-8688-36377dab82bf

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme
theorem _root_.solution {X : Scheme.{u}} (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U := by
  obtain ⟨U, hU, hxU, -⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens X)
      (show x ∈ (⊤ : X.Opens) from trivial)
  exact ⟨U, hxU, hU⟩
end AlgebraicGeometry.Scheme
