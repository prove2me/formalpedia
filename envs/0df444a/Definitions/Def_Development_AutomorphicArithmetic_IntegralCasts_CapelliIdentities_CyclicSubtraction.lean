-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CyclicSubtraction
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CyclicSubtraction
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:29.305537+00:00
-- url     : https://prove2.me/theorems/3060a0c8-ec5e-407f-bb0c-1f553ca007b0
-- title:
--   Cyclic Subtraction
-- statement:
--   Definitions and structural lemmas for Cyclic Subtraction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CyclicSubtraction.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.CyclicSubtraction.cycSub.{u_1, u_2} :
    {G : Type u_1} → {M : Type u_2} → [inst : Group G] → [inst_1 : AddCommGroup M] → Representation ℤ G M → G → M →+ M :=
    fun {G : Type u_1} {M : Type u_2} [Group G] [AddCommGroup M] (ρ : Representation ℤ G M) (σ : G) ↦
      ((ρ : G → M →ₗ[ℤ] M) σ - LinearMap.id).toAddMonoidHom


