-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_SmallCornerOfHeisenbergDual
-- name    : Development_AutomorphicSpectrum_Proofs_TwistedProofs_SmallCornerOfHeisenbergDual
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T16:29:09.942809+00:00
-- url     : https://prove2.me/theorems/47866de7-a176-429e-8dac-0050b0d4ff00
-- title:
--   Small Corner Of Heisenberg Dual
-- statement:
--   Definitions and structural lemmas for Small Corner Of Heisenberg Dual, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SmallCornerOfHeisenbergDual.lean

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
namespace GlobalTheory.CompanionTheory.InertCorner
variable {L : Type} [Field L] {N : ℕ}
def st (σ : L →+* L) (A : Matrix (Fin N) (Fin N) L) : Matrix (Fin N) (Fin N) L := fun i j => σ (A j.rev i.rev)
def dv (σ : L →+* L) (x : Fin N → L) : Fin N → L := fun j => σ (x j.rev)
def H (σ : L →+* L) (x : Fin N → L) (A : Matrix (Fin N) (Fin N) L) (y : Fin N → L) : L := x ⬝ᵥ (A *ᵥ dv σ y)
variable [Valued L (WithZero (Multiplicative ℤ))]
end GlobalTheory.CompanionTheory.InertCorner


