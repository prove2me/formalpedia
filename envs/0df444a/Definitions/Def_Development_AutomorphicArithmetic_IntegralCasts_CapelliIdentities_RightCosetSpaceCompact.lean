-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_RightCosetSpaceCompact
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_RightCosetSpaceCompact
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:09:55.70615+00:00
-- url     : https://prove2.me/theorems/701762dc-c67e-4cd7-ba59-41890a62476d
-- title:
--   Right Coset Space Compact
-- statement:
--   Definitions and structural lemmas for Right Coset Space Compact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/RightCosetSpaceCompact.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
@[reducible] noncomputable def UpperTheory.Reformulated.B.RightCosetSpaceCompact.RightCosetSpace.{u_1} :
    {G : Type u_1} → [inst : Group G] → Subgroup G → Type u_1 :=
    fun {G : Type u_1} [Group G] (Γ : Subgroup G) ↦ Quotient (MulAction.orbitRel (↥Γ) G)
noncomputable def UpperTheory.Reformulated.B.RightCosetSpaceCompact.mk.{u_1} :
    {G : Type u_1} → [inst : Group G] → (Γ : Subgroup G) → G → UpperTheory.Reformulated.B.RightCosetSpaceCompact.RightCosetSpace Γ :=
    fun {G : Type u_1} [Group G] (Γ : Subgroup G) ↦ Quotient.mk (MulAction.orbitRel (↥Γ) G)


