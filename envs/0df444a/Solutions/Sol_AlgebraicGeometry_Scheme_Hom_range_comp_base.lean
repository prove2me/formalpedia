-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Hom.range_comp_base
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:05.985593+00:00
-- url     : https://prove2.me/submissions/acebfd31-221f-48dd-b00a-3e20047caad5

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
open AlgebraicGeometry.Scheme.Hom
namespace AlgebraicGeometry.Scheme.Hom
theorem _root_.solution {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    Set.range (f ≫ g).base = g.base '' Set.range f.base := by
  have hcomp : ∀ x : A, (f ≫ g).base x = g.base (f.base x) := fun _ => rfl
  apply Set.Subset.antisymm
  · rintro z ⟨x, rfl⟩
    exact ⟨f.base x, ⟨x, rfl⟩, (hcomp x).symm⟩
  · rintro z ⟨y, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, hcomp x⟩
end AlgebraicGeometry.Scheme.Hom
