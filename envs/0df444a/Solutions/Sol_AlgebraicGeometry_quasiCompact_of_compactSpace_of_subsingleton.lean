-- Prove2me | solution 1 for AlgebraicGeometry.quasiCompact_of_compactSpace_of_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:39.876428+00:00
-- url     : https://prove2.me/submissions/043decc2-f09c-4c9f-8978-5554f86d38e7

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry
namespace AlgebraicGeometry
theorem _root_.solution {W S : Scheme.{u}} (f : W ⟶ S)
    [CompactSpace ↥W] [Subsingleton ↥S] : QuasiCompact f := by
  constructor
  intro U _ _
  rcases Set.eq_empty_or_nonempty (f.base ⁻¹' U) with h | ⟨w, hw⟩
  · rw [h]
    exact isCompact_empty
  · have h2 : f.base ⁻¹' U = Set.univ := by
      refine Set.eq_univ_of_forall fun w' => ?_
      have hww : f.base w' = f.base w := Subsingleton.elim _ _
      show f.base w' ∈ U
      rw [hww]
      exact hw
    rw [h2]
    exact isCompact_univ
end AlgebraicGeometry
