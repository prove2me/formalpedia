-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_PointwiseOfSpanHeisenberg
-- name    : Development_AutomorphicSpectrum_Proofs_TwistedProofs_PointwiseOfSpanHeisenberg
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T16:29:42.020466+00:00
-- url     : https://prove2.me/theorems/c3093c15-f863-463d-9708-fc259b0dbbd3
-- title:
--   Pointwise Of Span Heisenberg
-- statement:
--   Definitions and structural lemmas for Pointwise Of Span Heisenberg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/PointwiseOfSpanHeisenberg.lean

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
namespace GlobalTheory.CompanionTheory.InertLen
section Val
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
end Val
section Blocks
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
end Blocks
end GlobalTheory.CompanionTheory.InertLen
end


