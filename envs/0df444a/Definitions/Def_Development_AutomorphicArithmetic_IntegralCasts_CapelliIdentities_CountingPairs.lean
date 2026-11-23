-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CountingPairs
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CountingPairs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:02.263944+00:00
-- url     : https://prove2.me/theorems/a97dbc78-935c-430a-8974-d75da2e7019d
-- title:
--   Counting Pairs
-- statement:
--   Definitions and structural lemmas for Counting Pairs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CountingPairs.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.CountingPairs.rhoPair :
    {n : ℕ} → (Fin n → ℤ) → ℤ :=
    fun {n : ℕ} (l : Fin n → ℤ) ↦ ∑ i : Fin n, ((↑n : ℤ) - (1 : ℤ) - (2 : ℤ) * (↑(↑i : ℕ) : ℤ)) * l i
namespace UpperTheory.Reformulated.B.CountingPairs.Priv
end UpperTheory.Reformulated.B.CountingPairs.Priv


