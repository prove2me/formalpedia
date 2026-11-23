-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_AOpRightInvariant
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_AOpRightInvariant
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:23.410618+00:00
-- url     : https://prove2.me/theorems/0d2dc692-911d-4616-98ce-b3399d8e948b
-- title:
--   AOp Right Invariant
-- statement:
--   Definitions and structural lemmas for AOp Right Invariant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/AOpRightInvariant.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.Qf37.aOp :
    {G : Type} → [Group G] → Finset G → G → (G → ℂ) → G → ℂ :=
    fun {G : Type} [Group G] (R : Finset G) (t : G) (φ : G → ℂ) (g : G) ↦ ∑ r ∈ R, φ (g * r * t)


