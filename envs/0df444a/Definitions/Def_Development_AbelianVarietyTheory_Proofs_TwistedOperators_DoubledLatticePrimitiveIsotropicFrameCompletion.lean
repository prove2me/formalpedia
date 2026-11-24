-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DoubledLatticePrimitiveIsotropicFrameCompletion
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_DoubledLatticePrimitiveIsotropicFrameCompletion
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T16:33:22.842483+00:00
-- url     : https://prove2.me/theorems/1bb0bf94-718c-460c-9f8a-a21bb35d2a47
-- title:
--   Doubled Lattice Primitive Isotropic Frame Completion
-- statement:
--   Definitions and structural lemmas for Doubled Lattice Primitive Isotropic Frame Completion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DoubledLatticePrimitiveIsotropicFrameCompletion.lean

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
open Formalism.UG Matrix GlobalTheory.InertZeta GlobalTheory.SatakeWeyl
namespace GlobalTheory.FrameCompletion
section Basic
variable {L : Type} [Field L] {σ : L →+* L}
def gramQ (L : Type) [Field L] (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L :=
  fromBlocks (antiJ L n) 0 0 (-antiJ L n)
end Basic
section Int
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}
end Int
section Main
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
end Main
end GlobalTheory.FrameCompletion


