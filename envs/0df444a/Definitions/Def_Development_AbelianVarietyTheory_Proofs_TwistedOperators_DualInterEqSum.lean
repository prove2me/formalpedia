-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DualInterEqSum
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_DualInterEqSum
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T16:29:00.357379+00:00
-- url     : https://prove2.me/theorems/3bf36208-14c4-467c-8e3c-bd9b38722f47
-- title:
--   Dual Inter Eq Sum
-- statement:
--   Definitions and structural lemmas for Dual Inter Eq Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DualInterEqSum.lean

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
namespace GlobalTheory.InertZeta.DualLat
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {N : ℕ}
def tw (σ : L →+* L) (x : Fin N → L) : Fin N → L := fun j => σ (x j.rev)
def IntT (t : L) (x : Fin N → L) : Prop := ∀ i, t * x i ∈ intL L
end GlobalTheory.InertZeta.DualLat
namespace GlobalTheory.InertZeta
open DualLat
end GlobalTheory.InertZeta
end


