-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CosetInjective
-- name    : Development_AutomorphicSpectrum_Proofs_TwistedProofs_CosetInjective
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T16:28:41.33062+00:00
-- url     : https://prove2.me/theorems/49531859-ec5b-464f-8de2-cceebc36a60c
-- title:
--   Coset Injective
-- statement:
--   Definitions and structural lemmas for Coset Injective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CosetInjective.lean

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
namespace GlobalTheory.CompanionTheory.InertZeta
section
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
variable {N : ℕ}
end
end GlobalTheory.CompanionTheory.InertZeta
end


