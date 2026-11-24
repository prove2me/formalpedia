-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.presheaf_map_eq_of_parallel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:39.593007+00:00
-- url     : https://prove2.me/submissions/43c8fbb0-13d6-47c6-99a9-cdd45036b270

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
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme
theorem _root_.solution (X₁ : Scheme.{u}) {A B : (X₁.Opens)ᵒᵖ} (g₁ g₂ : A ⟶ B) :
    X₁.presheaf.map g₁ = X₁.presheaf.map g₂ :=
  congrArg X₁.presheaf.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _))
end AlgebraicGeometry.Scheme
