-- Prove2me | Definitions.Def_GroundTheory_LocalFields_FormalGroups_Truncation
-- name    : GroundTheory_LocalFields_FormalGroups_Truncation
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T11:11:55.666693+00:00
-- url     : https://prove2.me/theorems/674ba61f-6098-491b-a95f-79c792c9ffcd
-- title:
--   Truncation
-- statement:
--   Definitions and structural lemmas for Truncation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/FormalGroups/Truncation.lean

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsUniqueFixedPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.LocalField.FormalGroup
open MvPowerSeries
section Subst
variable {σ τ R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
def Close (n k : ℕ∞) (u v : MvPowerSeries τ S) : Prop :=
  k ≤ order u ∧ k ≤ order v ∧ n + k ≤ order (u - v) + 1
end Subst
section FixedPoint
variable {σ R : Type*} [CommRing R]
end FixedPoint
end GroundTheory.LocalField.FormalGroup


