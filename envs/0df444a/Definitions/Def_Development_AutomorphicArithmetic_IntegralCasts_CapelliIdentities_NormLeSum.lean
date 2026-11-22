-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormLeSum
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormLeSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:45:40.540247+00:00
-- url     : https://prove2.me/theorems/2e40fbd3-6fa8-4d40-86e8-f72b7d03a778
-- title:
--   Norm Le Sum
-- statement:
--   Definitions and structural lemmas for Norm Le Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/NormLeSum.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk34.MM :
    Nat → Nat → Type :=
    fun (P Q : Nat) ↦ Matrix (Sum (Fin P) (Fin Q)) (Sum (Fin P) (Fin Q)) Complex


