-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularSequenceLengthLeDim
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularSequenceLengthLeDim
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:01.968447+00:00
-- url     : https://prove2.me/theorems/a22ce2b6-921c-401b-a168-d276608c6cca
-- title:
--   St Regular Sequence Length Le Dim
-- statement:
--   Definitions and structural lemmas for St Regular Sequence Length Le Dim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StRegularSequenceLengthLeDim.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open IsLocalRing RingTheory.Sequence
universe u
def RegularSequenceLengthLeDim.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (rs : List R),
    (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular R rs → (rs.length : WithBot ℕ∞) ≤ ringKrullDim R
end GroundTheory.Heights₂.Heights


