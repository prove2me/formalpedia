-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_FractionExistsOfSmith
-- name    : Development_AutomorphicSpectrum_Proofs_TwistedProofs_FractionExistsOfSmith
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T17:04:58.830226+00:00
-- url     : https://prove2.me/theorems/f206513d-0568-4456-9963-5beaa02885e9
-- title:
--   Fraction Exists Of Smith
-- statement:
--   Definitions and structural lemmas for Fraction Exists Of Smith, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/FractionExistsOfSmith.lean

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
open Matrix
namespace GlobalTheory.CompanionTheory.InertZeta
open GlobalTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
end GlobalTheory.CompanionTheory.InertZeta


