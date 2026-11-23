-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsIntegralNatCast
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsIntegralNatCast
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:33:24.893638+00:00
-- url     : https://prove2.me/theorems/a7f23cb6-4411-4496-8c2e-2e918751c0ab
-- title:
--   Is Integral Nat Cast
-- statement:
--   Definitions and structural lemmas for Is Integral Nat Cast, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IsIntegralNatCast.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.IsIntegralNatCast.IsIntP :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → ℂ_[p] → Prop :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (x : ℂ_[p]) ↦ ‖x‖ ≤ (1 : ℝ)


