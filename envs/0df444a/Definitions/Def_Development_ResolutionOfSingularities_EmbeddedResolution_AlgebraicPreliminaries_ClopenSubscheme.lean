-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_ClopenSubscheme
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_ClopenSubscheme
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:20.948738+00:00
-- url     : https://prove2.me/theorems/cb220a7d-1d05-4ece-8af6-07cbb578d592
-- title:
--   Clopen Subscheme
-- statement:
--   Definitions and structural lemmas for Clopen Subscheme, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/ClopenSubscheme.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
namespace AlgebraicGeometry.Scheme.Opens
end AlgebraicGeometry.Scheme.Opens
namespace FunctorialResolution.EmbeddedResolution
def complOpensOfIsClosed {X : Scheme} (C : X.Opens) (hC : IsClosed (C : Set X)) : X.Opens :=
  ⟨(C : Set X)ᶜ, hC.isOpen_compl⟩
end FunctorialResolution.EmbeddedResolution


