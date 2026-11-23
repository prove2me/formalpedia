-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_Iwa
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_Iwa
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:51.744914+00:00
-- url     : https://prove2.me/theorems/c6e5338a-40b6-4667-97c5-0573a8653a9b
-- title:
--   Iwa
-- statement:
--   Definitions and structural lemmas for Iwa, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/Iwa.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.DYhc7.Iwa :
    {G : Type} → [inst : Group G] → Subgroup G → Subgroup G → Prop :=
    fun {G : Type} [Group G] (P K : Subgroup G) ↦ ∀ (g : G), ∃ p ∈ P, ∃ k ∈ K, g = p * k


