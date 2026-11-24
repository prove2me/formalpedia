-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralFundamentalDomainEqSum
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralFundamentalDomainEqSum
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T23:21:05.971445+00:00
-- url     : https://prove2.me/theorems/32aff791-c962-4004-82c5-4ac8c2ea0899
-- title:
--   Integral Fundamental Domain Eq Sum
-- statement:
--   Definitions and structural lemmas for Integral Fundamental Domain Eq Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralFundamentalDomainEqSum.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory IsDedekindDomain NumberField
namespace GlobalTheory.ClassIntegral
variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]
def dcoset (Γ K : Subgroup G) (g : G) : Set G := {x | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * g * k}
end GlobalTheory.ClassIntegral


