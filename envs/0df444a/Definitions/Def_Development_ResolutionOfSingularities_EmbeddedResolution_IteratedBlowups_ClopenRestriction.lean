-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:21.733945+00:00
-- url     : https://prove2.me/theorems/4d555563-0464-42ef-b427-da54c2a603bf
-- title:
--   Clopen Restriction
-- statement:
--   Definitions and structural lemmas for Clopen Restriction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/ClopenRestriction.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
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
def StrictNormalCrossingsRestrictToClopen : Prop :=
  ∀ (k : Type u) [Field k] (W : Scheme.{u}) (p : W ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] (E : List W.IdealSheafData) (Z : W.IdealSheafData),
    InStrictNormalCrossingPosition p E → HasStrictNormalCrossingsWith p Z E →
    ∀ U : (Z.subscheme).Opens, IsClosed (U : Set ↥(Z.subscheme)) →
    (∀ D ∈ E, ∀ T ∈ irreducibleComponents (↥(U.toScheme)),
        ¬ ((U.ι ≫ Z.subschemeι).base '' T) ⊆ (D.support : Set ↥W)) →
    IsStrictNormalCrossingsDivisor ((E.prod.comap (U.ι ≫ Z.subschemeι)).radical)
end FunctorialResolution.EmbeddedResolution


