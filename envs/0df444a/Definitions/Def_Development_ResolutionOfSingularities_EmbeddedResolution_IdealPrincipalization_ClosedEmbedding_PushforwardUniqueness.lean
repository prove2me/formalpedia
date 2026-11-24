-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_ClosedEmbedding_PushforwardUniqueness
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_ClosedEmbedding_PushforwardUniqueness
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:48.903851+00:00
-- url     : https://prove2.me/theorems/f26ebc64-ffab-42a8-91cd-e04e0af9868c
-- title:
--   Pushforward Uniqueness
-- statement:
--   Definitions and structural lemmas for Pushforward Uniqueness, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/ClosedEmbedding/PushforwardUniqueness.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_ClosedEmbedding_StrictTransformClosedImmersion
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
structure SequenceOfBlowupsPushforward {S X : Scheme.{u}} (j : S ⟶ X) (BS : SequenceOfBlowups S) (B : SequenceOfBlowups X) where
  lengthEq : BS.length = B.length
  σ : ∀ i : ℕ, i ≤ B.length → (BS.schemeAt i ⟶ B.schemeAt i)
  isClosedImmersion : ∀ (i : ℕ) (hi : i ≤ B.length), IsClosedImmersion (σ i hi)
  zero : σ 0 (Nat.zero_le B.length) ≫ B.isoZero.hom = BS.isoZero.hom ≫ j
  square : ∀ (i : ℕ) (hi : i < B.length),
    σ (i + 1) hi ≫ B.transitionMapSucc i = BS.transitionMapSucc i ≫ σ i hi.le
  center : ∀ (i : ℕ) (hi : i < B.length),
    B.center i = imageIdealSheaf (σ i hi.le) (BS.center i)
namespace SequenceOfBlowupsPushforward
end SequenceOfBlowupsPushforward
end FunctorialResolution.EmbeddedResolution


