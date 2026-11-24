-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_TraceIndexFormula
-- name    : Development_AutomorphicSpectrum_Proofs_TwistedProofs_TraceIndexFormula
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T16:39:38.641802+00:00
-- url     : https://prove2.me/theorems/ecc7d9ff-00da-4e68-9a58-b2e2d38b1c1f
-- title:
--   Trace Index Formula
-- statement:
--   Definitions and structural lemmas for Trace Index Formula, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/TraceIndexFormula.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceZeroIntegersModUniformizerCardOfCardSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardIntegersModUniformizerEqQSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta Formalism.UG
namespace GlobalTheory.CompanionTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
end GlobalTheory.CompanionTheory.InertZeta


