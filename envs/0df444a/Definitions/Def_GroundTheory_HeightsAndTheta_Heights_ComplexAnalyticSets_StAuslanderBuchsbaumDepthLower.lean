-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAuslanderBuchsbaumDepthLower
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAuslanderBuchsbaumDepthLower
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:10.591652+00:00
-- url     : https://prove2.me/theorems/4dcb9ea9-c97c-489b-bdf3-5d089edda3af
-- title:
--   St Auslander Buchsbaum Depth Lower
-- statement:
--   Definitions and structural lemmas for St Auslander Buchsbaum Depth Lower, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StAuslanderBuchsbaumDepthLower.lean

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
open IsLocalRing CategoryTheory RingTheory.Sequence
universe u
def AuslanderBuchsbaumDepthLower.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] (ℓ : ℕ) (rs : List R),
    HasProjectiveDimensionLE (ModuleCat.of R M) ℓ → (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular R rs →
      ∃ ms : List R, (∀ r ∈ ms, r ∈ maximalIdeal R) ∧ IsWeaklyRegular M ms ∧ ms.length = rs.length - ℓ
end GroundTheory.Heights₂.Heights


