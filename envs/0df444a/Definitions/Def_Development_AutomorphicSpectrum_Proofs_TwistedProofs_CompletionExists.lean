-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CompletionExists
-- name    : Development_AutomorphicSpectrum_Proofs_TwistedProofs_CompletionExists
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T16:32:41.499276+00:00
-- url     : https://prove2.me/theorems/7262e04e-f3b6-44bd-873a-8275b6b8cd1b
-- title:
--   Completion Exists
-- statement:
--   Definitions and structural lemmas for Completion Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CompletionExists.lean

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
open Formalism.UG Matrix GlobalTheory.InertZeta GlobalTheory.Doubling GlobalTheory.SatakeWeyl
namespace GlobalTheory.CompanionTheory.InertDoubling
section Cong
variable {L : Type} [Field L] {σ : L →+* L} {m p : Type}
end Cong
section Int
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
end Int
section Main
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
end Main
end GlobalTheory.CompanionTheory.InertDoubling


