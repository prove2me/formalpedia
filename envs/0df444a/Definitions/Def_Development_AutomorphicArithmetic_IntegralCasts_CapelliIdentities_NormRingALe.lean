-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormRingALe
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormRingALe
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T21:32:03.799491+00:00
-- url     : https://prove2.me/theorems/39c5c4e1-bf8f-4905-a901-a5fb8258d022
-- title:
--   Norm Ring ALe
-- statement:
--   Definitions and structural lemmas for Norm Ring ALe, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/NormRingALe.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.Qi27.muPrime :
    (l : ℕ) → [inst : Fact (Nat.Prime l)] → Set ℂ_[l] :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ {ζ : ℂ_[l] | ∃ (n : ℕ), (0 : ℕ) < n ∧ ¬l ∣ n ∧ ζ ^ n = (1 : ℂ_[l])}
noncomputable def UpperTheory.Reformulated.B.Qi27.ringA :
    (l : ℕ) → [inst : Fact (Nat.Prime l)] → Subring ℂ_[l] :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ Subring.closure (UpperTheory.Reformulated.B.Qi27.muPrime l)


