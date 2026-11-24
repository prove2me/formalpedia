-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_RecursionIdentity
-- name    : Development_AutomorphicSpectrum_Proofs_TwistedProofs_RecursionIdentity
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T16:26:51.508976+00:00
-- url     : https://prove2.me/theorems/1a57a7c0-5b27-45ea-ab62-7d3a9c337122
-- title:
--   Recursion Identity
-- statement:
--   Definitions and structural lemmas for Recursion Identity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/RecursionIdentity.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.InertZeta
namespace GlobalTheory.CompanionTheory.InertLevi
def aTerm (q N : ℕ) (X α : ℂ) (a : ℤ) : ℂ :=
  (q : ℂ) ^ ((2 * N + 2) * a.toNat) * X ^ a.natAbs * (α ^ a * (q : ℂ) ^ (-a * ((N : ℤ) + 1)))
end GlobalTheory.CompanionTheory.InertLevi
end


