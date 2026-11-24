-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_KrullDimClosedSubset
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_KrullDimClosedSubset
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T12:31:00.051205+00:00
-- url     : https://prove2.me/theorems/a7be3ac3-0b31-4fed-a78b-c282d9bbae31
-- title:
--   Krull Dim Closed Subset
-- statement:
--   Definitions and structural lemmas for Krull Dim Closed Subset, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/KrullDimClosedSubset.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open TopologicalSpace AlgebraicGeometry
namespace FunctorialResolution.EmbeddedResolution
def irreducibleClosedsImageSubtypeVal {X : Type u} [TopologicalSpace X] {Y : Set X} (hY : IsClosed Y)
    (a : IrreducibleCloseds ↥Y) : IrreducibleCloseds X :=
  ⟨Subtype.val '' a.1, a.2.image _ continuous_subtype_val.continuousOn,
    hY.isClosedMap_subtype_val _ a.3⟩
def irreducibleClosedsMapHomeomorph {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (a : IrreducibleCloseds X) : IrreducibleCloseds Y :=
  ⟨e '' a.1, a.2.image e e.continuous.continuousOn, e.isClosedMap _ a.3⟩
end FunctorialResolution.EmbeddedResolution


