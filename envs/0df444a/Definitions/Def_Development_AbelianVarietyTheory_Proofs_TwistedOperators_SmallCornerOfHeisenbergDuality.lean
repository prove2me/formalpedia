-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmallCornerOfHeisenbergDuality
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmallCornerOfHeisenbergDuality
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T16:28:59.215795+00:00
-- url     : https://prove2.me/theorems/093a4078-c77a-4ae9-b2fc-fdf6970474da
-- title:
--   Small Corner Of Heisenberg Duality
-- statement:
--   Definitions and structural lemmas for Small Corner Of Heisenberg Duality, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SmallCornerOfHeisenbergDuality.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
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
section Herm
variable {L : Type} [Field L] {N : ℕ}
def hermJ (σ : L →+* L) (x y : Fin N → L) : L := ∑ i, σ (x i) * y i.rev
end Herm
section Unitary
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
end Unitary
end GlobalTheory.InertZeta


