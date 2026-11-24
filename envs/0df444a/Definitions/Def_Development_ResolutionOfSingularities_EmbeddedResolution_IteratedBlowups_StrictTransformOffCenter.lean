-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransformOffCenter
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransformOffCenter
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:54:02.33115+00:00
-- url     : https://prove2.me/theorems/34e15f84-a549-45e0-b9f3-e1f33b7ee4d0
-- title:
--   Strict Transform Off Center
-- statement:
--   Definitions and structural lemmas for Strict Transform Off Center, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/StrictTransformOffCenter.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
def complComapSupport {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z : X.IdealSheafData) : X₁.Opens :=
  (Z.comap π).support.compl
end FunctorialResolution.EmbeddedResolution


