-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_affineOpens_mem_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:39:48.684031+00:00
-- url     : https://prove2.me/submissions/1497c3cc-99db-45ed-b6e2-b5db27ae8e6d

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
theorem _root_.solution {X : Scheme.{u}} {x : X} {U : X.Opens} (hx : x ∈ U) :
    ∃ V : X.affineOpens, x ∈ V.1 ∧ V.1 ≤ U := by
  obtain ⟨V, hV, hxV, hsub⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  obtain ⟨W, hW, rfl⟩ := hV
  exact ⟨⟨W, hW⟩, hxV, hsub⟩
end AlgebraicGeometry.Scheme
