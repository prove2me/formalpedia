-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_DualPairingExists
-- name    : Development_AutomorphicSpectrum_Proofs_TwistedProofs_DualPairingExists
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T16:29:42.082813+00:00
-- url     : https://prove2.me/theorems/08f930a7-6d31-4732-bcc1-97c34c22e65b
-- title:
--   Dual Pairing Exists
-- statement:
--   Definitions and structural lemmas for Dual Pairing Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/DualPairingExists.lean

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
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
namespace GlobalTheory.CompanionTheory.InertDual
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {N : ℕ}
end GlobalTheory.CompanionTheory.InertDual
end


