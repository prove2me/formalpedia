-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Hom.appLE_congr_hom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:28.52525+00:00
-- url     : https://prove2.me/submissions/2bc72f0e-b387-4842-863b-452432a51761

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
theorem _root_.solution {A B : Scheme.{u}} {f g : A ⟶ B} (hfg : f = g) (O : B.Opens)
    (S : A.Opens) (h1 : S ≤ f ⁻¹ᵁ O) (h2 : S ≤ g ⁻¹ᵁ O) :
    Scheme.Hom.appLE f O S h1 = Scheme.Hom.appLE g O S h2 := by
  subst hfg
  rfl
end AlgebraicGeometry.Scheme.Hom
