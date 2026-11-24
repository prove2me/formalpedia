-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CosetSurjectiveOfLevi
-- name    : Development_AutomorphicSpectrum_Proofs_TwistedProofs_CosetSurjectiveOfLevi
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T16:34:27.477883+00:00
-- url     : https://prove2.me/theorems/967bc0a6-a956-44d3-9f3e-b004b645a5fa
-- title:
--   Coset Surjective Of Levi
-- statement:
--   Definitions and structural lemmas for Coset Surjective Of Levi, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CosetSurjectiveOfLevi.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryLeviNormalizesUnipotentRadical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryBlockTriangularLeviPartUnitary
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
namespace GlobalTheory.CompanionTheory.InertCoset
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
def hf (σ : L →+* L) (x y : Fin n → L) : L := ∑ k, σ (x k.rev) * y k
def refl (σ : L →+* L) (d : Fin n → L) : Matrix (Fin n) (Fin n) L := 1 + Matrix.of fun i j => d i * σ (d j.rev)
section Levi
variable {N : ℕ} {ϖ : L} {a a' : ℤ} {g g' : GU σ N} {m m' : GU σ (N + 2)}
end Levi
end GlobalTheory.CompanionTheory.InertCoset
end


