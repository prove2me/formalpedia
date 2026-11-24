-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumSpherical
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumSpherical
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T16:26:07.227899+00:00
-- url     : https://prove2.me/theorems/2e7f9778-6279-46c8-b7fa-b04d51a90ad1
-- title:
--   Has Sum Spherical
-- statement:
--   Definitions and structural lemmas for Has Sum Spherical, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSumSpherical.lean

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
open Formalism.UG Matrix GlobalTheory.SatakeWeyl
namespace GlobalTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {ϖ : L} {q N : ℕ}
end GlobalTheory.InertZeta
end


